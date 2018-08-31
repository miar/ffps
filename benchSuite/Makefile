# Tested with JDK 10.0.1
# Make sure that JDK and JDK_PATH are OK. 
# I assuming that you have Java in  ~/.bin directory. Please change it otherwise.

JDK_PATH = ~/bin
JDK = jdk-10.0.1/bin
TEST = MultiThreadBenchRunner

MultiThreadBenchRunnerAll:
	make GetUpdatedFFPO
	$(JDK_PATH)/$(JDK)/javac *.java
#       $(JDK_PATH)/$(JDK)/java  -server $(TEST) generateNewDataset  CHM     CSLM    NBHM     CT     FFP    > tmp/map_results
#       $(JDK_PATH)/$(JDK)/java  -server $(TEST) generateNewDataset  CHM     CSLM    CT       FFPO   FFPS    > tmp/map_results
	$(JDK_PATH)/$(JDK)/java  -server $(TEST)      "true"        "true"  "false" "false" "false" "false" > tmp/CHM
	$(JDK_PATH)/$(JDK)/java  -server $(TEST)      "false"       "false" "true"  "false" "false" "false" > tmp/CSLM
	$(JDK_PATH)/$(JDK)/java  -server $(TEST)      "false"       "false" "false" "true"  "false" "false" > tmp/CT
	$(JDK_PATH)/$(JDK)/java  -server $(TEST)      "false"       "false" "false" "false" "true"  "false" > tmp/FFPO
	$(JDK_PATH)/$(JDK)/java  -server $(TEST)      "false"       "false" "false" "false" "false" "true"  > tmp/FFPS
	make clean

GetUpdatedFFPO:
	cp ../ffpo/src/* ffpo/
	cd ffpo ; $(JDK_PATH)/$(JDK)/javac -XDignore.symbol.file *.java	

clean: 
	rm *.class

