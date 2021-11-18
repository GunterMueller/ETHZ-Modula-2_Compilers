Source Code form some "accient" Modula-2 Compilers from the ETHZ. Forked from http://www.cfbsoftware.com/modula2/.
========================================================
From the "https://www.cfbsoftware.com/modula2/" WebSite

 Introduction

The programming language Modula-2 was authored by Professor Niklaus Wirth of the Institut fur Informatik of the Swiss Federal Institute of Technology (ETH) in 1979. A joint software / hardware project, in conjunction with the language development produced the advanced programmers' workstation Lilith in 1980. Software developed for the Lilith computer included a compiler, operating system, text and graphic editors and other support software:

    ETH Report Nr 40 - The Personal Computer Lilith (The Yellow Report). Apr 1981. N. Wirth
    ETH Report Nr 40 (PDF file 1.5 MB)

Multi-Pass Modula-2 Compiler Sources (Lilith M-code)

Professor Niklaus Wirth has kindly given us permission to make the following items publicly available here:

    M2M Compiler Sources. Modula Research Institute. Oct 1983
    M2M Compiler Sources (Zip file 180 KB)

The first Modula-2 compiler was completed in 1979 and ran on the DEC PDP-11. This is the source code of the PC version of the second Modula-2 compiler. It generates M-code for the Lilith and can be compiled and run on a PC using the M2M-PC System (see below). The following text document files are included with the sources:

    Overview of the Modula-2 Compiler M2M
    Files on Tape for M2M Compiler
    The M-code interpreter (Appendix 1 of the Yellow Report)

The appendix includes a table of the M-Code instructions and the Modula-2 source of the M-Code intepreter providing a high-level definition of the Lilith computer's instruction set and architecture.

    The M2M-PC System - v1.35 for MS-DOS. Modula Research Institute. Feb 1984
    M2M-PC v1.35 for MS-DOS (Zip file 120 KB)

The M2M-PC System is an M-code interpreter which allows the Lilith Modula-2 compiler and its output to be executed on the IBM-PC running MS-DOS 2.0 or later. Refer to the Modula-2 Handbook for instructions on how to use the system:

    The Modula-2 Handbook - A Guide for Modula-2 Users and Programmers. Nov 1983. Modula Research Institute 
    The Modula-2 Handbook (PDF file 1.8 MB)

Single-Pass Modula-2 Compiler Source Code (Lilith M-code)

    A Single-pass Modula-2 Compiler for Lilith, N.Wirth, Nov 1985 
    Release Notes (3 pp PDF file 166 KB) 
    Compiler Sources (Zip file 200 KB)

The third Lilith Modula-2 compiler was released in 1985. It is a single-pass compiler developed by J. Gutknecht and N. Wirth and compiles about four times faster than the earlier multi-pass compiler. The source code went missing for many years but was eventually located in Nov 2021 by Jos Dreesen, the designer of the remarkable Lilith emulator EmuLith.

An executable version of this compiler named SYS.compile.OBJ exists on several of the disk images (e.g. Dsk1.img) included with EmuLith. It can be used to compile these sources using the Medos commandfile M2SP.COM that accompanies the source files.
Single-Pass Modula-2 Compiler Source Code (Mac 68000)

    MacMeth Compiler Sources. Copyright 1992 Departement Informatik ETH Zuerich
    MacMeth Compiler Sources (Zip file 202 KB)

This source code is of a version of the single-pass compiler which generates native code for the Motorola MC68000 and MC68040 microprocessors. Refer to the file copyright contained in the zip file for the relevant licensing conditions.

Two versions of the compiler are included. They correspond to the versions of the language as described in the Third (1985) and Fourth Editions (1988) of the reference:

   Programming in Modula-2, N. Wirth, published by Springer-Verlag.

These compilers are used in the Apple Macintosh Modula-2 system MacMETH. The MacMETH User Manual contains detailed operational information about the compilers:

   MacMETH 3.2. A Fast Modula-2 Language System For the Apple Macintosh - User Manual.
   Wirth, N., Gutknecht, J., Heiz, W., Schär, H.R., Seiler, H., Vetterli, C. & Fischlin, A. (1992).
   Departement Informatik ETH Zürich. 4th, completely revised edition, Release 3.2. (116 pp PDF file 732 KB)

A copy of this manual can be downloaded from the MacMeth website
Related Dissertations

    Code Generation and the Lilith Architecture, C. Jacobi. ETH Zurich, 1982.  
    Diss. ETH No 7195 (108 pp PDF file 30.5 MB)

    Separate Compilation in Modula-2 and the Structure of the Modula-2 Compiler on the Personal Computer Lilith, L. Geissmann. ETH Zurich, 1983.  
    Diss. ETH No 7286 (64 pp PDF file 22.3 MB)

