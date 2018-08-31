
Lock-Free Fixed Persistent And Sorted Hash Map (FFPS)

Steps to compare Concurrent Hash Maps (CHM), Concurrent Skip Lists
(CSL), Concurrent Tries (CT) and FFP(O-Original and S-Sort) models in
Linux using a terminal emulator:

1. git clone git@github.com:miar/ffps.git

2. cd ffp/benchSuite/

3. mkdir tmp

4. Open the Makefile file, update JDK_PATH and JDK with your system
values, close Makefile and do 'make' in the terminal

5. Results with execution times and memory used by each model will
appear in the 'tmp' directory

6. If you want to see how our model is implemented check the 'ffp' and
'ffps' directories.

Enjoy it.