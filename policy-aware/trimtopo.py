import codecs
import time
import random
import sys
import getopt

#from node import *
#from asqueue import *
from topo import Topo


# This program will read in a big topology and trim it into a smaller one
# use dag-base-waypoint-nexthop-paper.topo

class Usage(Exception):
    def __init__(self, msg):
        self.msg = msg



def gen_smalltopo(opts):
    list = []
    for i in range(50, 1050, 50):
        list.append(i)
    for opt, arg in opts:
        if opt == "-r":
            topo = Topo(arg)
            for num in list:
                topo.gen_smalltopo("topos/15169small" + str(num) + ".txt", num, 15169)


def gen_intratopo(rrnum = 10, clientnum = 100):
    total = rrnum + clientnum
    topo = Topo("topos/emptytopo.txt")
    topo.gen_intratopo(rrnum = rrnum, clientnum = clientnum, ofile = "topos/intratopo_" + str(total) + ".txt")

def main(argv = None):
    if argv is None:
        argv = sys.argv
    try:
        try:
            opts, args = getopt.getopt(argv[1:], "hr:", ["relationfile="])
        except getopt.error as msg:
            raise Usage(msg)
    except Usage as err:
        print>>sys.stderr, err.msg
        print >> sys.stderr, "for help use --help"
        return 2
    print(opts)
    print(args)

#    gen_smalltopo(opts)
    for i in range(1, 11):
        gen_intratopo(rrnum = i * 10, clientnum = i * 90)


if __name__ == '__main__':
    sys.exit(main())
