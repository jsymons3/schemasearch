from collections import namedtuple
from collections import OrderedDict
from operator import itemgetter
import threading
from multiprocessing.pool import ThreadPool
import time
import csv
import guiSkelly
import pickle
from pickle import Pickler
from scipy import stats
from scipy.stats import stats
import os
import sys
import logging
import tkinter.ttk
from tkinter import *
from tkinter import messagebox
import time
from threading import Thread
import traceback
import itertools

#read
tolerance = 0.00001;# select a tolerance of 5 decimal places
#similar to a struct. Named tuple of floats
Data_vals = namedtuple("Data_vals", "onset_beats,duration_beats,channel,pitch,velocity,onset_sec,duration_sec,piece,loc_list")
Loc_conc = namedtuple("Loc_conc", "concordance_pattern,location,hard_location")
matrix_partition_counter=200000000# will set aside 200MB for the temporary matrix storage. Used in process overlap/

"""Partiton counter limits the amount of memory for the count value table"""
partition_counter = 4500000

INT_SIZE = sys.getsizeof(int())

FLOAT_SIZE = sys.getsizeof(float())

LIST_SIZE= sys.getsizeof(list())


def compFloat(f1,f2):
    """This function takes two floats,compares them to a tolerance and returns a boolean if they are equal"""
    #first check if both are integers
    if f1.is_integer() and f2.is_integer():
        if int(f1)==int(f2):
            return True
        else:
            return False

    if abs(f1-f2) < tolerance and abs(f2-f1) < tolerance:
        return True
    return False


class ConcordanceApp:
    """The wrapper for the application. all methods are called through this class. gui is contained within as well"""
    def __init__(self):
        """Initializer class"""

        self.openLoc=[]#openfile location
        self.saveLoc = []#savefile loc
        self.track = None # track level
        self.beats =None# interval between beats
        self.conc_length = None # n gram length
        self.query_counter = 0#keeps track of the number of queries
        self.total_counter=0
        self.base_store_file = "overlap" # name of overlap disk file
        self.base_matrix_file = "matrix" # name of matrix disk file
        self.p_matrix_file = "pmatrix"  # name of pmatrix file
        self.countvaluetable = dict()
        self.basstable = dict()
        self.melodytable = dict()

        """These variables will be linked to tkinter checkboxes that determine the flow of the program.phase 1,2,3"""
        self.chkp1=None
        self.chkp2=None
        self.chkp3 = None
        """These variables are linked to tkinter labels to update the program state periodically"""
        self.out1=None
        self.out2=None
        self.out3=None

        self.winref=None # a reference to the gui
        self.root=None

        """These variables keep track of the number of files we write to the disk temporarily to not run out of memory"""
        self.file_counter=0 # keeps track of our current file counter. used in phase 2
        self.matrix_file_counter=0 # keepts track of our matrix file counter.used in phase 2
        self.pmatrix_file_counter=0 # pmatrix file counter. used in phase 3
        self.logger = None
        """These variables are used in phase 2 and 3"""
        self.local_countvaluetable= dict()
        #self.local_total_counter=0
        self.local_basstable = dict() # dictionary of bass intersection counters
        self.local_melodytable = dict()# dictionary of melody intersection counters
        self.thread_tk=None#our 2nd thread for the additional gui
        """these are used for the querys"""
        self.query_range = None# guiSkelly.addEntry(self.root,1,4)
        self.pitch_range = None# guiSkelly.addEntry(self.root,1,4)
        self.query_box = None
        self.querystart = None
        self.querylist = None
        self.chkModulo = None
        self.chkPreserve = None
        self.query_length= 0


    def initialize(self):
        """Initialize a gui and class varaibles for the program"""

        #Set up the labels on the gui. requires a root window, label description,row position, column position
        self.root = guiSkelly.loadSkelly()
        self.root.title("Schema Discovery and Search")
        label_qrange = guiSkelly.addLabel(self.root, "Maximum displacement (beats)",9,2)
        label_prange = guiSkelly.addLabel(self.root,"Vertical interval",10,2)
        label_line = guiSkelly.addLabel(self.root,"        " ,0,4)
        label_query = guiSkelly.addLabel(self.root,"Input pattern." ,8,1)


        self.query_range =  guiSkelly.addEntry(self.root,9,3)
        self.pitch_range =  guiSkelly.addEntry(self.root,10,3)
        self.querylist = guiSkelly.addListBox(self.root,13,1)
        self.query_length= 0 # temporary workaround

        #Set up buttons on the gui. requires root window, button name, function to call on click,variable to save results, row position,column position
        button4 = guiSkelly.addDefaultButton(self.root,"Add Pattern",self.addListEntry,10,1)
        buttondelete = guiSkelly.addDefaultButton(self.root,"Remove Patterns", self.removeListEntry,14,1)
        button5 = guiSkelly.addDefaultButton(self.root, "Start Search",self.phaseIV,13,5)

        # column 5, row 12?s
        self.query_box = guiSkelly.addEntry(self.root,9,1)
        self.winref=tkinter.Toplevel(self.root)#make a 2nd window
        self.nmat = None
        self.chkModulo = guiSkelly.addChkbtn(self.root, "Use Modulo",10,4)
        self.chkPreserve = guiSkelly.addChkbtn(self.root, "Preserve Order",9,4)
        self.chkPreserve.set(1)#enable checkbox

        #Set up labels  and text on the  2nd gui. Requires 2nd root window, label tag, row,position.
        self.out1 = guiSkelly.addLabel(self.winref,"Ready                           ",4,2)
        self.out2 = guiSkelly.addLabel(self.winref,"Ready                           ",5,2)
        self.out3 = guiSkelly.addLabel(self.winref,"------------------------                           ",6,2)
        self.winref.title("musicAnalyzer2.1(Working)")
        self.winref.geometry("400x70")
        self.winref.withdraw()
        self.winref.protocol("WM_DELETE_WINDOW",self.onExit)

        # NOW initialize the logger
        self.logger = logging.getLogger('musicAnalyzer2_3')
        hdlr = logging.FileHandler('musicAnalyzer2_3.log')
        formatter = logging.Formatter('%(asctime)s %(levelname)s %(message)s')
        hdlr.setFormatter(formatter)
        self.logger.addHandler(hdlr)
        self.logger.setLevel(logging.WARNING)

    def addListEntry(self):
        """Adds an item into the list box"""
        self.querylist.insert(END,self.query_box.get())

    def removeListEntry(self):
        """Removes selected items from the list box"""
        items = self.querylist.curselection()
        pos = 0
        for i in items :
            idx = int(i) - pos
            self.querylist.delete( idx,idx )
            pos = pos + 1

    def errorRespond(self,e):
        self.logger.error(e)

    def loadData(self,file_in="giantnotematrix.csv"):
        """Read a matrix in string form and convert it into a list of tuple"""
        self.out2.set("Reading in " + file_in)
        list_dataVals = []
        counter=0
        #Matrix =  list(namedtuple)
        try:
            with open(file_in,newline='') as csvfile:
                spamreader = csv.reader(csvfile)
                for splits in spamreader:
                    #splits = line.split()
                    onset = float(splits[0])
                    #print(onset)
                    duration = float(splits[1])
                    channel=int(splits[2])
                    pitch = float(splits[3])
                    velocity = float(splits[4])
                    onset_sec = float(splits[5])
                    duration_sec=float(splits[6])
                    piece=float(splits[7])
                    next_row = Data_vals(onset,duration,channel,pitch,velocity,onset_sec,duration_sec,piece,list())
                    list_dataVals.append(next_row)
                    counter+=1
                    #if counter>10000:
                    #    break
        except Exception as e:
            self.out3.set("Error reading in file")
            print(e)
            #self.errorRespond(e)
            tb = traceback.format_exc()
            print(tb)
            self.errorRespond(tb)
        self.nmat = list_dataVals

        return list_dataVals


    def cleanUp(self):
        """Here we clear out the temporary files"""

        self.out1.set("Cleaning temp files(pass 1) ")
        print("File counter: " + str(self.file_counter))

        for x in range(0,self.file_counter):
            try:
                #print("Clean file" + str(file_counter))

                os.remove(self.base_store_file + str(x)+ ".p")
                self.out2.set("Removed file" + str(x+1) +  "out of " + str(self.file_counter))
            except  Exception as e:
                print(e)
                self.errorRespond(e)
        self.out1.set("Cleaning temp files(pass 2) ")
        for x in range(0,self.matrix_file_counter):
            try:
                #print("Clean file" + str(matrix_file_counter))
                os.remove(self.base_matrix_file + str(x)+ ".p")
                self.out2.set("Removed file" + str(x+1) +  "out of " + str(self.matrix_file_counter))
            except Exception as e:
                print(e)
                self.errorRespond(e)

        self.out1.set("Cleaning temp files(pass 3) ")
        for x in range(0,self.pmatrix_file_counter):
            try:
                #print("Clean file" + str(matrix_file_counter))
                os.remove(self.p_matrix_file + str(x)+ ".p")
                self.out2.set("Removed file" + str(x+1) +  "out of " + str(self.pmatrix_file_counter))
            except Exception as e:
                print(e)
                self.errorRespond(e)
        self.out1.set("Cleanup finished")


    def startProgram(self,root,args):
        """This function starts the program and returns a tuple of concordances,locationList"""
        self.thread_tk=Thread(target=self.start,args=(self.root,))
        self.thread_tk.start()


    def start(self,root):

        starttime = time.clock()#start the clock
        try:
            if self.chkp1.get()==1:
                self.cleanUp()#cleanup the temporary files
            else:
                pass

            endtime=time.clock()

            print("elapsed:time")
            print(endtime)
            self.out1.set("Finished. Closing in 5.")
            time.sleep(5)
            self.root.destroy()
            os._exit(0)
        except Exception as e:
            print(e)
            tb = traceback.format_exc()
            print(tb)
            self.out3.set("Error in phase 2/3.")
            self.logger.error(e)
            self.logger.error(tb)
            self.cleanUp()
            #errorRespond(e)
            #os._exit(0)
            sys.exit()

    def onExit(self):
        if messagebox.askokcancel("Quit", "Are you sure you want to quit?"):
            self.winref.master.destroy()
            #clean up the thread here
            self.thread_tk.exit()
            #os._exit(0)#quit()
            sys.exit()

    def parse(self):
        queryarguments = list()

        """ loop through the list box and collect the query results individually"""
        entries = list(self.querylist.get(0, END))
        for item in entries:
            pitchpatterns = item.split(r";")[0].split(r",")#split pattern and rise/fall. Then subsplit into individual items
            n_gramlength = len(pitchpatterns)
            risefall = item.split(r";")[1].split(r",")# array of intervals
            #print(risefall)
            queryarguments.append((pitchpatterns,risefall,n_gramlength))
        self.query_counter = len(entries) # get the number of args
        self.query_length = n_gramlength
        return queryarguments

    def query(self,queryarguments):
        """takes: list of tuples of pattern, intervals, and len. Returns locations where query results occurs
            Goal: get a corpus(matrix) and a list of concordances to query.
            Steps: First query for the first concordance. Get the locations from this result and then call process row with the positional argument changed.
            Repeat this for each subset"""
        try:
            beat_displacement = float(self.query_range.get())
        except:
            beat_displacement  = None
        try:
            vertical_distance = int(self.pitch_range.get())
        except:
            vertical_distance = None
        qur = iter(queryarguments) #iterator to our query list
        next_suite = next(qur) # next tuple to process. includes pitch patttern, beat pattern
        next_query = next_suite[0]
        relative_start_search_position = 0
        #rise_fall = iter(queryarguments[0][1])

        next_risefall = next_suite[1] #next pitch pattern

        resultlist=list()
        combolist = list()
        templist = list()
        initialresult = None
        length = len(self.nmat)
        #print(queryarguments[0][0])
        """ Here is a new change. If the order isn't preserved, then that means we have to find all permutations  of size length and search for them as well.
                A query of length 4 yields 9 differeent possibilities or 9 different results. Now if two queries of length 4 are processed, that yields 81 different queries to run.Not recommended"""

        if self.chkPreserve.get()==0: # not preserving order
            """ get the permutations"""
            possible_permutations = self.query_permutations(next_query)
            #print(possible_permutations)
            #now process all permutations
            #solo_start_search_position = self.getAbsolutePosition(beat_displacement,resultlist[0][0])#get the absolute position from the first pattern.added
            for pattern in possible_permutations:
                #print( pattern)
                for x in range(0,length): # loop through our matrix and find locations of the first query. Store locations in resultlist
                    #print("Working row " + str(x) + " out of " + str(length))

                    initialresult =self.processQueryRow(pattern,next_risefall,x) # check
                    if initialresult is not None:
                        #print("valid")
                        resultlist.append(initialresult) #
        else:
            for x in range(0,length): # loop through our matrix and find locations of the first query. Store locations in resultlist
                #print("Working row " + str(x) + " out of " + str(length))
                initialresult =self.processQueryRow(next_query,next_risefall,x) # check
                if initialresult is not None:
                    #print("valid")
                    resultlist.append(initialresult) #

            #gc.collect()
        if len(queryarguments) <2: # if we only had one queryargument, end the search
            print("One query inserted")
            templist = list()
            for item in resultlist:
                templist.append((item,))
            return templist

        next_suite = next(qur) # set iterator to next tuple of data
        next_query = next_suite[0] # get the next query
        next_risefall = next_suite[1] # get the next interval pattern


        """ Check if we are doing permutations"""
        if self.chkPreserve.get()==0:
            permutations_level_two = self.query_permutations(next_query)
        #print("Result for query one")
        #print(resultlist)
        while 1: #loop until our list is empty
            try:
                if len(resultlist) < 1:
                    return resultlist
                relative_start_search_position = self.getAbsolutePosition(beat_displacement,resultlist[0][0])#get the absolute position from the first pattern.added

                for x in resultlist: # for all locations found so far, look for successive query patterns starting from them
                    for y in range(relative_start_search_position,length): #for y in range(x[0],length):
                        if self.chkPreserve.get()==0:
                            for pattern in permutations_level_two:
                                initialresult = self.processQueryRow(pattern,next_risefall,y)
                                if initialresult is not None:
                                    combolist.append(initialresult)
                        else:
                            initialresult =self.processQueryRow(next_query,next_risefall,y) # check
                            if initialresult is not None:

                                combolist.append(initialresult) #


                for item in resultlist: # check to see if the results from combolist are within range with the results from result list
                    for item2 in combolist:
                        #print('comparing ' + str(item[2]) + ' to ' + str(item2[2]) + ' = ' +  str(abs(item[2]) - item2[2] ))

                        if vertical_distance is not None:
                            #print("vertical distance exists")
                            if  (abs(item[2] - item2[2])<= beat_displacement) and (abs(item[1] - item2[1])== vertical_distance) and (item[4] ==item2[4]) and self.chkModulo.get()==0:
                                templist.append((item,item2))
                                break
                            elif self.chkModulo.get()==1:# modulo operator is checked
                                #print('checking modulo')
                                if  abs(item[2] - item2[2])<= beat_displacement and (abs(item[1] - item2[1]) % 12)== vertical_distance and (item[4]==item2[4]):
                                    #print('checking modulo 2')
                                    #print(str(item[1] + "," + str(item2[1])))
                                    templist.append((item,item2))
                                    break
                        else:
                            if  abs(item[2] - item2[2])<= beat_displacement and (item[4] == item2[4]):
                                templist.append((item,item2))
                                break

                resultlist.clear()
                resultlist = templist.copy()
                templist.clear()
                combolist.clear()
                next_suite = next(qur)
                next_query = next_suite[0]
                next_risefall = next_suite[1]
            except StopIteration:
                #print("finished")
                return resultlist

        return resultlist

    def processQueryRow(self,concordance,interval_pattern, position):
        """concordance is a list describing the pattern to match. interval pattern is the corresponding interval list. table_data is the matrix,position is the slot in the matrix we are looking for"""

        """     Goal: Analyze a row in the matrix and determine if it is the start of a query result.
                Steps: Get the next pattern to match(1 enntryfromm both concorance and interval pattenr) and inspect the next row seeing if the change in pitch/interval matches the next pattern. If so set a flag , save location, and repeat until
                        next returns bad/null or we go past the max distance allowed. Return the position, and location info
        """
        #import pdb; pdb.set_trace()

        #objgraph.show_growth(limit=10)
        working_row= self.nmat[position] # the row in the table we are analyzing
        current_track = working_row.channel # the track number we will be looking at when analyzing this row
        #current_piece = working_row.piece
        interval_pattern_ints = [float(nums) for nums in interval_pattern] # convert to numberic format
        #max_distance =  sum(interval_pattern_ints)+ working_row.onset_beats# the maximum distance allowed to find a match
        max_distance = max(interval_pattern_ints) + working_row.onset_beats
        #print(str(max(interval_pattern_ints)) + " : max for this row starting at position " + str(position+1))
        #print (max_distance)
        current_pitch = working_row.pitch# the initial pitch we're starting at
        initial_pitch = float(working_row.pitch)
        initial_piece = int(working_row.piece)
        current_beat=float(working_row.onset_beats)# the starting beat
        beat_iterator = iter(interval_pattern_ints[1:]) # get an iterator to the pitch list
        pitch_iterator = iter(concordance[1:])# get an iterator to the concordance list
        counter = 1
        output_form_list=[]

        #next_pitch = float(next(pitch_iterator))
        next_pitch = next(pitch_iterator)

        """ modify the next pitch. next pitch should not convert to a float. instead check if it has a pipe"""
        next_beat = float(next(beat_iterator))
        output_form_list.append((position,current_beat, initial_pitch,0,0.0))

        #print("initial pitcj = " + str(current_pitch) + " initial beat = " + str(current_beat))
        for x in range(position+1, len(self.nmat)):
            try:
                current_row = self.nmat[x] # look at the next row in the table to compare to the current row
                current_pitch = current_row.pitch
                #print("Row" + str(position+1))
                #print( "current putch: " + str(current_row.pitch) + "next pitch " + str(next_pitch) + "comparison pitch" + str(current_pitch) +  "current beat: " + str(current_row.onset_beats) + "next beat " + str(next_beat) )
               ## if current_track!=current_row.channel: # skip this row
                 #   print("unveven channel")
                    #continue
                if current_row.piece != initial_piece or current_row.onset_beats> max_distance  :
                    del working_row
                    del current_track
                    interval_pattern_ints.clear()
                    del interval_pattern_ints
                    del current_pitch

                    del pitch_iterator
                    del beat_iterator

                    del next_beat
                    del next_pitch
                    #print(counter)
                    #print ("max distance exceeded " + str(max_distance) + " " + str(current_row.onset_beats))
                    del current_beat
                    del max_distance
                    del current_row
                    return None# end the search query


                # special case for when the next beat is 0

                split_by_pipe_list = next_pitch.split(r"|")

                if split_by_pipe_list== None:#check if we have a valid object.if not, make it valid
                    split_by_pipe_list = list()
                    split_by_pipe_list.append(next_pitch)

                #not we have a list with each separate pitch

                pipe_counter = len(split_by_pipe_list)
                matched_counter = 0
                matched_list = list()#holds list of matched pipes

                if next_beat == 0:


                    nextitem = self.find_Pattern_Using_Zero_Beat_Level(x, current_row.onset_beats,current_row.pitch,next_pitch,initial_pitch,next_beat)
                    if nextitem:#if we found a match
                        #print(nextitem)
                        counter+=1
                        output_form_list.append(nextitem)
                        if counter==len(concordance):
                            #print("success ")
                            return (position+1,initial_pitch,current_beat,output_form_list,initial_piece)
                        #next_pitch = float(next(pitch_iterator))
                        next_pitch = next(pitch_iterator)
                        next_beat = float(next(beat_iterator))
                    continue #skip the next if check


                #print( "pitch comparison: " + str(next_pitch + initial_pitch) + "to " + str(current_row.pitch)  + "beat comparison " + str(next_beat + current_beat) + str(current_row.onset_beats))
                #pipe_counter = next_pitch.count(r"|")#count the number of seperate occurences


                for y in range(0,pipe_counter):#loop through and try to match each next pitch in the list. if all match, we have a successful loop
                    if compFloat(current_row.pitch,float(split_by_pipe_list[y]) + initial_pitch)  and compFloat(current_row.onset_beats ,next_beat + current_beat) :# check to see if the pitches match.
                    # set a flag to store location and continue
                        matched_counter+=1
                        matched_list.append(split_by_pipe_list[y])

                if matched_counter>0:
                    #print(matched_counter)
                    #print(matched_list)
                    counter+=1
                    n_pitch = ""
                    if len(matched_list)==1:
                        n_pitch = "".join(matched_list)
                    else:
                        n_pitch = r"|".join(matched_list)
                    #print(n_pitch)
                    output_form_list.append((x,current_row.onset_beats, current_pitch,n_pitch, next_beat))
                    if counter==len(concordance):
                        #print("success ")
                        return (position+1,initial_pitch,current_row.onset_beats,output_form_list,initial_piece)
                    next_pitch = next(pitch_iterator)
                    next_beat = float(next(beat_iterator))
                    pass
            except StopIteration:
                # we have cauth the pattern
                #print("Out of iterables")
                #print("counter: " + str(counter) + " length: " + str(len(concordance)))
                if counter == len(concordance):
                    return x
                return None

            except Exception as e:
                self.errorRespond(e)
                tb = traceback.format_exc()
                #print(tb)
                self.errorRespond(tb)
                pass# log to error logger
                #print("exception occured")
                return None
        return None

    def phaseIV(self):
       args = self.parse()
       #if self.nmat is None:
       self.loadData(self.openLoc[0])
       print(self.openLoc[0])
       outtext= self.query(args)
       #print(outtext)
       formatString = "Row#\tBEAT\t\tPITCH\t\tP Pat\t\tB Pat  | \t"
       for x in range(1, self.query_counter):
            formatString += "Row#\tBEAT\tPITCH\t\tP Pat\t\tB Pat\t  |"
       formatString+= "\n"
       output = ""
       fname = 'QueryOut.txt'
       with open(fname,'a+') as f:
           print(formatString)
           f.write(formatString)

           # now print out the data in readable form
           print(str(len(outtext)) + " results found")
           f.write(str(len(outtext)) + " results found\n")
           q_counter = 1
           for item in outtext:
                #print(item)
                print("Query Result " + str(q_counter) )
                f.write("Query Result " + str(q_counter) + "\n")

                for x in range(0, self.query_length): # need  concordance length not counter
                    """ Things are about to get  really ugly...just don't ask. debugging this took hours >_>"""
                    for y in range(0, self.query_counter):#(item[x][3])): #item [x][3] is the list containning
                        output+= str(item[y][3][x][0]) + "\t\t" +   ('%5s' % str(item[y][3][x][1])) + "\t\t" + ('%5s' % str(item[y][3][x][2])) +  "\t\t" + ('%5s' % str(item[y][3][x][3])) + "\t\t" + ('%5s' % str(item[y][3][x][4])) + "  | \t"
                #print(item)
                    print(output)
                    f.write(output)
                    print("\n")
                    f.write("\n")
                    output=""
                    #print(str(another_layer[0]) + "\t\t" + str(another_layer[1]) + "\t\t" +str(another_layer[2]) + "\t\t"+str(another_layer[3]) + "\t\t\t"+str(another_layer[4]) )
                q_counter +=1

    def getAbsolutePosition(self,displacement_max,startposition,):
        """ Searches for a position in the matrix to search relative to a starting point.
            arg1: beat displacement max, arg2: starting position to begin search at
        """
        lastposition = startposition
        max_val_to_find = self.nmat[startposition].onset_beats - displacement_max
        for x in range(startposition,0,-1):
            if self.nmat[lastposition].onset_beats >= max_val_to_find :
                lastposition = x
            else:
                break

        return lastposition

    def query_permutations(self,in_list):
        """ Finds all permuations of a pattern and converts from tuples to lists.Keeps 0 in the first slot"""
        outlists = []
        out = []
        #out = itertools.permutations(sample[1:])
        outlists = [x for x in itertools.permutations(in_list[1:])]
        for e in outlists:
            out.append(["0"] + list(e))
        return out

    def find_Pattern_Using_Zero_Beat_Level(self, start_position,beat,pitch,next_pitch,initial_pitch, next_beat):
        """Searches a partition of the matrix to check for a specific pattern/beat that has a 0 rise/fall from the previous note.
            arg1:starting position of where the search for 0 occurs."""

        """  Algorithm: Takes a row in n_mat matrix and expands upwards until beat fall < 0 amd expands downward until beat rise >0.
        In that partition, it explicitly searches for the next matching pitch. Returns row data if found, else None"""

        split_by_pipe_list = next_pitch.split(r"|")

        if split_by_pipe_list== None:#check if we have a valid object.if not, make it valid
           split_by_pipe_list = list()
           split_by_pipe_list.append(next_pitch)

                #not we have a list with each separate pitch
        pipe_counter = len(split_by_pipe_list)
        matched_counter = 0
        matched_list = list()

        starting_row = self.nmat[start_position]
        starting_piece = starting_row.piece
        for x in range(start_position,0,-1): #loop from the current row upwards
            current_row = self.nmat[x]
            if current_row.onset_beats!= beat: # if our beat doesnt match, break
                break

            if current_row.piece!= starting_piece:# if our pieces dont match, break the loop
                break
            #print("Analyzing row " + str(x) + " starting from position " + str(start_position))
            #print("lower current pitch, initial pitch, next pitch " + str(current_row.pitch) + " " + str(initial_pitch) + " " + str(next_pitch))
            for y in range(0,pipe_counter):
                if compFloat(current_row.pitch,float(split_by_pipe_list[y]) + initial_pitch) :# check to see if the pitches match.
                    #print("returning a lower match")
                    matched_counter+=1
                    matched_list.append(split_by_pipe_list[y])
            if matched_counter>0:
                n_pitch = ""
                if len(matched_list)==1:
                    n_pitch = "".join(matched_list)
                else:
                    n_pitch =  r"|".join(matched_list)
                return (x,current_row.onset_beats, current_row.pitch,n_pitch, next_beat)
        # else loop from the current row downwards

        matched_counter = 0# reset the counter


        for x in range(start_position,len(self.nmat)): #loop from the current row downwards
            current_row = self.nmat[x]
            if current_row.onset_beats!= beat: # if our beat doesnt match, break
                break

            if current_row.piece!= starting_piece:# if our pieces dont match, break the loop
                break

            #print("upper current pitch, initial pitch, next pitch " + str(current_row.pitch) + " " + str(initial_pitch) + " " + str(next_pitch))

            for y in range(0,pipe_counter):
                if compFloat(current_row.pitch,float(split_by_pipe_list[y]) + initial_pitch) :# check to see if the pitches match.
                    #print("returning a lower match")
                    matched_counter+=1
                    matched_list.append(split_by_pipe_list[y])
            if matched_counter>0:
                if len(matched_list)==1:
                    n_pitch = "".join(matched_list)
                else:
                    n_pitch = r"|".join(matched_list)
                return (x,current_row.onset_beats, current_row.pitch,n_pitch, next_beat)

        return None


def main():
    x=ConcordanceApp()
    try:
        x.initialize()
        x.root.mainloop()
    #thread_tk=Thread(target=createWorkerWindow)# create the mini gui
    #thread_tk.start()# start the mini gui thread
        #root.mainloop()
    except Exception as e:
        tb = traceback.format_exc()
        print(e)
        print(tb)
        x.cleanUp()
        print("successfully cleaned resources")
        #os._exit(0)
    #os._exit(0)
    sys.exit()

if __name__ == '__main__':
    main()
