# Coins_Compiler-Infrastructure
----------------------------------------------------------------------
  Copyright (C) 2007 Association for the COINS Compiler Infrastructure
      (Read COPYING for detailed information.)
----------------------------------------------------------------------

2015/05/25  1.5
  Add a new SSA optimizer "Scalar replacement based on demand-driven
  partial redundancy elimination" and new options presrhir, presr,
  eqp, divex3 related to the new optimizer.
  Remove bugs of inline expansion.

2013/07/25  1.4.6
  Add optimization options glia, expde, ddpde, 
    and complexityAllowance. 
  Remove bugs of C-frontend.

2012/05/25  1.4.5.2 
  Add the extended register promotion that is invoked by new option
    -coins:regpromote-ex.
  Remove bugs of HIR optimization and HIR-to-C.

2011/10/31  1.4.5.1
  Bugs of HIR2C for loop statements were corrected.
  Build operation was done in Java 5 environment to generate
    class files to be distributed.
   (Build operation of coins-1.4.5 was done in Java 6 environment.)

2011/08/30  1.4.5
  LIR numbering facilities were added and some source line information
  is kept even after SSA optimization.
    (See SSA options ssa-opt=stlin, etc.)
  Facilities of counting executed LIR instructions for each basic block 
    were added. (See SSA option cntbb.)
  Bugs of HIR optimization, data flow analysis, snapshot, etc. were fixed.
  Documents on visualization, parallelization, coins-option, etc. 
