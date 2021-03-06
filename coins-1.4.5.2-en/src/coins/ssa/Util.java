/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.ssa;

import coins.backend.Function;
import coins.backend.Op;
import coins.backend.util.BiList;
import coins.backend.util.BiLink;
import coins.backend.lir.LirNode;
import coins.backend.lir.LirLabelRef;
import coins.backend.cfg.BasicBlk;
import coins.backend.cfg.FlowGraph;
import coins.backend.util.ImList;
import coins.backend.Type;
import coins.backend.sym.Symbol;
import coins.backend.sym.Label;

import java.util.Stack;

/**
 * Utilities for the SSA module
 **/
class Util{
  /** The environment of the SSA module **/
  private SsaEnvironment env;
  /** The current function **/
  private Function f;

  /** 
   * Constructor
   * @param e The environment of the SSA module
   * @param function The current function
   **/
  Util(SsaEnvironment e,Function function){
    env=e;
    f=function;
  }

  /**
   * Make a new JUMP node to the specified label.
   * @param blk The basic block which the new JUMP node put in
   * @param labelRef The label which the new JUMP node go to
   * @return A new JUMP node
   **/
  LirNode makeNewJump(BasicBlk blk,LirLabelRef labelRef){
    LirNode newJump=env.lir.operator(Op.JUMP,Type.UNKNOWN,
                                     labelRef,ImList.Empty);
    //env.output.println(newJump);
    BiLink q=blk.instrList().last();
    q.addBefore(newJump);
    q.unlink();
    blk.maintEdges();
    f.flowGraph().touch();

    return(newJump);
  }

  /**
   * Search and find the LIR nodes which has the specified operation code.
   * @param root The root node of the search
   * @param opCode The specified operation code
   * @param l The list which is stored in the found LIR node
   * @return The list of LIR nodes
   **/
  BiList findTargetLir(LirNode root,int opCode,BiList l){
    if(root!=null){
      if(root.opCode==opCode){// && !l.contains(root)){
        //env.output.println("Util.java : "+root);
        l.add(root);
      }
      for(int i=0;i<root.nKids();i++){
        l=findTargetLir(root.kid(i),opCode,l);
      }
    }
    return(l);
  }

  /**
   * Change the LabelRef node into the SSA specified ones.
   * Or Change the LabelRef node into the normal ones.
   * This method MUST be called before translating into SSA form.
   * @param isTranslate True if the translation is for the specified ones
   **/
  void changeLabelRef(boolean isTranslate){
    FlowGraph g=f.flowGraph();
    BasicBlk entry=g.entryBlk();
    for(BiLink p=g.basicBlkList.first();!p.atEnd();p=p.next()){
      BasicBlk blk=(BasicBlk)p.elem();
      for(BiLink q=blk.instrList().first();!q.atEnd();q=q.next()){
        LirNode node=(LirNode)q.elem();
        //env.output.println(node);
        switch(node.opCode){
          case Op.JUMP:{
            LirNode newLabel;
            if(isTranslate)
              newLabel=env.lir.labelRefVariant(((LirLabelRef)node.kid(0)).label);
            else
              newLabel=env.lir.labelRef(((LirLabelRef)node.kid(0)).label);
            
            node.setKid(0,newLabel);
            //env.output.println("---> "+node);
            break;
          }
          case Op.JUMPC:{
            for(int i=1;i<node.nKids();i++){
              LirNode newLabel;
              if(isTranslate)
                newLabel=env.lir.labelRefVariant(((LirLabelRef)node.kid(i)).label);
              else
                newLabel=env.lir.labelRef(((LirLabelRef)node.kid(i)).label);
              
              node.setKid(i,newLabel);
            }
            //env.output.println("---> "+node);
            break;
          }
          case Op.JUMPN:{
            //env.output.println(1+" : "+node.kid(1));          
            for(int i=0;i<node.kid(1).nKids();i++){
              LirNode newLabel;
              if(isTranslate)
                newLabel=env.lir.labelRefVariant(
                  ((LirLabelRef)node.kid(1).kid(i).kid(1)).label);
              else
                newLabel=env.lir.labelRef(
                  ((LirLabelRef)node.kid(1).kid(i).kid(1)).label);
              
              node.kid(1).kid(i).setKid(1,newLabel);
            }
            //env.output.println(2+" : "+node.kid(2));
            LirNode newLabel;
            if(isTranslate)
              newLabel=env.lir.labelRefVariant(((LirLabelRef)node.kid(2)).label);
            else
              newLabel=env.lir.labelRef(((LirLabelRef)node.kid(2)).label);
            
            node.setKid(2,newLabel);
            //env.output.println("---> "+node);
            break;
          }
        }
      }
    }
  }

  /**
   * Collect the edges from the predecessors or predecessors themselves.
   * @param blk The current basic blk
   * @param getPredBlk True means to collect predecessors
   * @return The list of edges or basic blocks
   **/
  BiList predEdges(BasicBlk blk,boolean getPredBlk){
    BiList edges=new BiList();

    for(BiLink p=blk.predList().first();!p.atEnd();p=p.next()){
      BasicBlk pred=(BasicBlk)p.elem();
      Label[] target=((LirNode)pred.instrList().last().elem()).getTargets();
      for(int i=0;i<target.length;i++){
        if(blk.label().basicBlk()==target[i].basicBlk()){
          if(getPredBlk) edges.add(pred);
          else edges.add(target[i]);
        }
      }
    }

    return(edges);
  }

  /**
   * Make a new Phi instruction.
   * The arguments and the variable that defined by this new Phi instruction
   * have the specified symbol.
   * @param s The specified symbol
   * @param blk The basic block which the new phi instruction is inserted
   * @return A new Phi instruction
   **/
  LirNode makePhiInst(Symbol s,BasicBlk blk){
    BiList edges=predEdges(blk,false);
    BiList preds=predEdges(blk,true);
    LirNode[] args=new LirNode[edges.length()+1];
    int argNum=0;

    // Make a destination operand
    args[argNum]=env.lir.symRef(Op.REG,s.type,s,ImList.Empty);
    argNum++;

    // Make source operands
    for(BiLink p=preds.first();!p.atEnd();p=p.next()){
      BasicBlk pred=(BasicBlk)p.elem();
      LirNode[] anArg=new LirNode[3];
      anArg[0]=env.lir.symRef(Op.REG,s.type,s,ImList.Empty);
      //anArg[1]=f.labelRef(Op.LABEL,Type.ADDRESS,pred.label(),ImList.Empty);
      anArg[1]=env.lir.labelRefVariant(pred.label());

      // Get third argument of Phi node
      Label targetLabel=blk.label();
      LirNode predJump=(LirNode)pred.instrList().last().elem();

      //env.output.println(predJump);

      if(predJump.opCode==Op.JUMP){
        LirLabelRef labelRef=(LirLabelRef)predJump.kid(0);
        if(targetLabel.basicBlk()==labelRef.label.basicBlk()){
          boolean isOK=true;
          for(int i=1;i<argNum;i++){
            if(args[i].kid(2)!=null && 
               ((LirLabelRef)args[i].kid(2)).variant==labelRef.variant){
              isOK=false;
            }
          }
          if(isOK){
            anArg[2]=labelRef;
            //env.output.println(" : found "+anArg[2]);
          }
          //else env.output.println(" : not found 1 : "+anArg[2]);
        }
        //else env.output.println(" : not found 2");
      }
      else if(predJump.opCode==Op.JUMPC){
        boolean isFound=false;
        for(int i=1;i<predJump.nKids();i++){
          LirLabelRef labelRef=(LirLabelRef)predJump.kid(i);
          if(targetLabel.basicBlk()==labelRef.label.basicBlk()){
            boolean isOK=true;
            for(int j=1;j<argNum;j++){
              if(args[j].kid(2)!=null && 
                 ((LirLabelRef)args[j].kid(2)).variant==labelRef.variant){
                isOK=false;
              }
            }
            if(isOK){
              //env.output.println(" : found "+labelRef);
              isFound=true;
              anArg[2]=labelRef;
            }
          }
        }
        //if(!isFound) env.output.println(" : not found 3");
      }
      else if(predJump.opCode==Op.JUMPN){
        boolean isFound=false;
        for(int i=0;i<predJump.kid(1).nKids();i++){
          LirLabelRef labelRef=
            (LirLabelRef)predJump.kid(1).kid(i).kid(1);
          if(targetLabel.basicBlk()==labelRef.label.basicBlk()){
            boolean isOK=true;
            for(int j=1;j<argNum;j++){
              if(args[j].kid(2)!=null && 
                 ((LirLabelRef)args[j].kid(2)).variant==labelRef.variant){
                isOK=false;
              }
            }
            if(isOK){
              //env.output.println(" : found "+labelRef);
              isFound=true;
              anArg[2]=labelRef;
            }
          }
        }
        if(!isFound){
          LirLabelRef labelRef=(LirLabelRef)predJump.kid(2);
          if(targetLabel.basicBlk()==labelRef.label.basicBlk()){
            boolean isOK=true;
            for(int i=1;i<argNum;i++){
              if(args[i].kid(2)!=null &&
                 ((LirLabelRef)args[i].kid(2)).variant==labelRef.variant){
                isOK=false;
              }
            }
            if(isOK){
              //env.output.println(" : found in default "+labelRef);
              anArg[2]=labelRef;
            }
            //else env.output.println(" : not found 4");
          }
          //else env.output.println(" : not found 5");
        }
      }
      else{
        System.err.println("TranslateToSsa.java : Unexpected LIR node : "+
                           predJump);
        System.exit(1);
      }

      
      args[argNum]=env.lir.operator(Op.LIST,Type.UNKNOWN,anArg,ImList.Empty);
      argNum++;
    }

    // Make Phi instruction
    LirNode phiInst=env.lir.operator(Op.PHI,s.type,args,ImList.Empty);
    //env.output.println(phiInst+"\n");

    return(phiInst);
  }
}
