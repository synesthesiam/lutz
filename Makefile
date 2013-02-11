SRC = main.cpp
BIN_DIR = bin
OUTPUT = $(BIN_DIR)/hmd

$(OUTPUT): $(SRC)
	mkdir -p $(BIN_DIR)
	g++ -Wno-deprecated -g -o $(OUTPUT) $(SRC)

