#!/bin/bash
#TODO: remove redundancy of "-R ~~" with Makefile
coqdep -dumpgraph graph.dot \
    -R ../lib compcert.lib -R ../common compcert.common -R ../x86 compcert.x86  -R ../x86_64 compcert.x86_64 \
    -R ../backend compcert.backend -R ../cfrontend compcert.cfrontend -R ../driver compcert.driver \
    -R ../flocq compcert.flocq -R ../exportclight compcert.exportclight -R ../cparser compcert.cparser \
    -R lib compcomp -R common compcomp -R x86 compcomp -R x86_64 compcomp -R backend compcomp \
    -R cfrontend compcomp -R compose compcomp -R proof compcomp -R bound compcomp -R demo compcomp \
    **
dot -Tpng graph.dot > graph.png
