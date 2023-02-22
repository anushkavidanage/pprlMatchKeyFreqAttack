Frequency based privacy attack on Multiple Dynamic Match-key encoding for PPRL
==============================================================================

Anushka Vidanage, Thilina Ranbaduge, Peter Christen, and Sean Randall

Paper title: A Privacy Attack on Multiple Dynamic Match-key based 
             Privacy-Preserving Record Linkage\
Paper URL: [here](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7893850/)

Copyright 2020 Australian National University and others.
All Rights reserved.

See the file LICENSE for the terms under which the computer program
code and associated documentation in this package are licensed.

08 February 2020.

Contact: anushka.vidanage@anu.edu.au

-------------------------------------------------------------------

Requirements:
=============

The Python programs included in this package were written and
tested using Python 2.7.6 running on Ubuntu 16.04

The following extra packages are required:
- numpy
- scipy

Running the attack program:
===========================

To run the program, use the following command (with an example setting):

  python pprl_match_key_freq_attack.py path-to-encode-dataset.csv.gz 
         0 , True path-to-plaintext-dataset.csv.gz 0 , True 100 attack 
         7.0 comb main 20

For moe details about the command line arguments see comments at the top of 
'pprl_match_key_freq_attack.py'
