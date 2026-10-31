CXX ?= g++
CXXFLAGS ?= -O3 -march=native -std=c++20 -Wall -Wextra -Wpedantic -fopenmp

all: lean

lean:
	lake build

check:
	bash scripts/check.sh

comparator:
	bash scripts/palomar/verify-comparator.sh

paper:
	latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/macmahon-min-universal-sets.tex

regenerate:
	python3 scripts/generate_lean_data.py

cubes: build/cubes

build/cubes: src/cubes.cpp
	mkdir -p build
	$(CXX) $(CXXFLAGS) $< -o $@

.PHONY: all lean check comparator paper regenerate cubes
