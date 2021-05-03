BUILD_DIR = build
INSTALL_INCLUDE_DIR = /usr/local/include/ecstk

CFLAGS = -Wall -Wextra -Wno-missing-braces -pedantic -O2 -std=c++20
CPP = g++

tests-buffer:
	$(CPP) $(CFLAGS) tests/main.cc -o $(BUILD_DIR)/tests-buffer

clean:
	rm -f $(BUILD_DIR)/*

install:
	mkdir -p $(INSTALL_INCLUDE_DIR)
	cp src/*.hh $(INSTALL_INCLUDE_DIR)

uninstall:
	rm $(INSTALL_INCLUDE_DIR)/buffer.hh
