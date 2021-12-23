PROFILE:=0
DEBUG?=0
CC=gcc
CXX:=g++
LD=g++
STATIC?=0
CPLEX?=0

ifeq ($(PROFILE), 1)
    PGFLAGS:=-pg
else
    PGFLAGS:=
endif

ifeq ($(DEBUG), 1)
    DBGFLAGS:=-g
    OPTFLAGS:=
else
    DBGFLAGS:=
    OPTFLAGS:=-O3
endif

ifeq ($(STATIC), 1)
	STATIC_LIBS:=-lpthread -ldl
	LD_STATIC:=-static
endif

# CUDD vars
CUDDROOT=../cudd-2.5.0/
CUDDINCLUDE=-I${CUDDROOT}/include/
CUDDLIBS=$(CUDDROOT)cudd/libcudd.a $(CUDDROOT)util/libutil.a  $(CUDDROOT)obj/libobj.a $(CUDDROOT)/epd/libepd.a $(CUDDROOT)mtr/libmtr.a $(CUDDROOT)st/libst.a $(CUDDROOT)dddmp/libdddmp.a
CUDDLIBRARIES=-L$(CUDDROOT)cudd/ -L$(CUDDROOT)util/  -L$(CUDDROOT)obj/ -L$(CUDDROOT)/epd/ -L$(CUDDROOT)mtr/ -L$(CUDDROOT)st/ -L$(CUDDROOT)dddmp/
CUDDLIBFLAGS=-lobj -ldddmp -lcudd -lmtr -lst -lutil -lepd

# minisat vars
MINISATROOT=../minisat/
MINISATLIB=${MINISATROOT}/core/lib_release.a
MINISATINCLUDE=-I${MINISATROOT}

# cmsat vars
CMSATROOT=../cmsat-2.9.9/
CMSATLIB=$(CMSATROOT)/build/cmsat/.libs/libcryptominisat.a
CMSATLIBRARIES=-L$(CMSATROOT)/build/cmsat/.libs/
CMSATINCLUDE=-I${CMSATROOT} # -I${CMSATROOT}/build
CMSATLIBFLAGS=-lcryptominisat
CMSATSO=$(CMSATROOT)/build/cmsat/.libs/libcryptominisat.so $(CMSATROOT)/build/cmsat/.libs/libcryptominisat-2.9.9.so

# lgl vars.
LGLROOT=../lingeling/
LGLLIB=$(LGLROOT)/liblgl.a
LGLLIBRARIES=-L$(LGLROOT)
LGLINCLUDE=-I${LGLROOT}
LGLLIBFLAGS=-llgl

INCLUDE=${MINISATINCLUDE} ${CPLEXINCLUDE} ${CUDDINCLUDE} ${CMSATINCLUDE} ${LGLINCLUDE}
LIBS=-lfl -lz -lgomp ${LGLLIBFLAGS} -ldl ${STATIC_LIBS}
DEFINES=-D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -D IL_STD ${CPLEXDEFINES} # -D HAVE_CONFIG_H

# CPLEX defines.
ifeq ($(CPLEX), 1)
	CPLEXINCLUDE:=-I/opt/ibm/ILOG/CPLEX_Studio128/cplex/include/ -I/opt/ibm/ILOG/CPLEX_Studio128/concert/include/
	CPLEXLIBRARIES:=-L/opt/ibm/ILOG/CPLEX_Studio128/concert/lib/x86-64_linux/static_pic/ -L/opt/ibm/ILOG/CPLEX_Studio128/cplex/lib/x86-64_linux/static_pic/
	CPLEXLIBFLAGS:=-lilocplex -lcplex -lconcert -lm -lpthread
	CPLEXDEFINES:=-DCPLEX_ENABLED
else
	CPLEXINCLUDE:=
	CPLEXLIBRARIES:=
	CPLEXLIBFLAGS:=
	CPLEXDEFINES:=
endif

CXXFLAGS:=-c -Wall -Werror -Wno-error=deprecated -fopenmp -std=c++0x ${INCLUDE} ${DEFINES} ${DBGFLAGS} ${OPTFLAGS} ${PGFLAGS} ${LD_STATIC} -Wno-strict-overflow # -Wno-unused-result -Wno-unused-function
LFLAGS:=-c -Wall ${INCLUDE} ${DEFINES} ${DBGFLAGS} ${OPTFLAGS} ${PGFLAGS} # -Wno-unused-result -Wno-unused-function
LDFLAGS:=${DBGFLAGS} ${OPTFLAGS} ${PGFLAGS} $(CUDDLIBRARIES)  ${CPLEXLIBRARIES}  $(CMSATLIBRARIES) ${LGLLIBRARIES} ${LD_STATIC}
SUFFIXES += .d

#Find all the C++ files in the current directory.
SOURCES:=$(shell find . -name "*.cpp" | grep -v mcqd.cpp)
#These are the dependency files, which make will clean up after it creates them
DEPFILES:=$(patsubst %.cpp,%.d,$(SOURCES))
#Objects
OBJECTS:=$(patsubst %.cpp,%.o,$(SOURCES))

all:sld sle lcmp lcheck lle simplify

lle: sld
	rm -f lle
	ln -s sld lle

sle: sld
	rm -f sle
	ln -s sld sle

lcmp: sld
	rm -f lcmp
	ln -s sld lcmp

lcheck: sld
	rm -f lcheck
	ln -s sld lcheck

simplify: sld
	rm -f simplify
	ln -s sld simplify

sld: lex.yy.o bench.tab.o ${MINISATLIB} ${CMSATLIB} ${LGLLIB} ${CUDDLIBS} $(OBJECTS) 
	$(LD) $(LDFLAGS) -o sld $(OBJECTS) ${CMSATLIB} lex.yy.o bench.tab.o ${MINISATLIB} ${CPLEXLIBFLAGS} ${CUDDLIBFLAGS} ${LIBS}  

lex.yy.o: lex.yy.cc bench.tab.cc
	$(CXX) $(LFLAGS) lex.yy.cc

bench.tab.o: bench.tab.cc ast.h
	$(CXX) $(CXXFLAGS) bench.tab.cc

lex.yy.cc: bench.l 
	flex -o lex.yy.cc bench.l

bench.tab.cc: bench.y ast.h
	bison -d -Werror -rall -o bench.tab.cc bench.y

# This is the rule for creating the dependency files
%.d: %.cpp
	$(CXX) $(CXXFLAGS) -MM $< > $@

# This include statement pulls in the commands to build the .o files.
include $(subst .cpp,.d,$(SOURCES))

clean:
	rm -f sld sle lcmp *.o *.cc *.hh *.output *.d

test: sld lcmp
	python3 test.py short

testall: sld lcmp
	python3 test.py all

.PHONY: clean test testall
