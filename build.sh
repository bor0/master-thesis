#!/bin/bash
pandoc \
	--pdf-engine=xelatex \
	--listings -H data/setup.tex \
	-B data/header.tex \
	-s --toc \
	$(paste -s -d " " sections.txt) \
	metadata.yaml \
	--output thesis.pdf
