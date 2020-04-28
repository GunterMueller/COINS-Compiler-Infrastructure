/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.util;

public final class IntLive {

// field

  private final IntConst val;

// member type

  private abstract static class Shift {
    abstract IntConst eval(IntConst c,int n);
  }
  private static Shift SHIFT_LSH=new Shift() {
    IntConst eval(IntConst c,int n) { return c.lsh(n); }
  };
  private static Shift SHIFT_RSHU=new Shift() {
    IntConst eval(IntConst c,int n) { return c.rshu(n); }
  };
  private static Shift SHIFT_RSHS=new Shift() {
    IntConst eval(IntConst c,int n) { return c.rshs(n); }
  };

// constructor

  private IntLive(IntConst val) { this.val=val; }

// factory method

  public static IntLive valueOf(int size) { return new IntLive(IntConst.valueOf(size,0).bnot()); }
  public static IntLive empty(int size) { return new IntLive(IntConst.valueOf(size,0)); }
  public static IntLive valueOf(IntConst val) { return new IntLive(val); }

// method

  public IntLive union(IntLive l) { return valueOf(val.bor(l.val)); }
  public IntLive intersection(IntLive l) { return valueOf(val.band(l.val)); }
  public IntLive inheritAdd() {
    return valueOf(propagateRight(val));
  }
  public IntLive inheritAdd(IntConst c) {
    return valueOf(propagateRight(val).band(rightmostOne(c).neg()).bor(val));
  }
  public IntLive inheritSub0() { return inheritAdd(); }
  public IntLive inheritSub1() { return inheritAdd(); }
  public IntLive inheritSub0(IntConst c1) { return inheritAdd(c1.neg()); }
  public IntLive inheritSub1(IntConst c0) {
    // ~(x-y) = y-x-1 = (-x-1)+y = ~x+y
    return inheritAdd(c0.bnot());
  }
  public IntLive inheritMul() { return inheritAdd(); }
  public IntLive inheritMul(IntConst c) {
    if(c.size()!=val.size()) throw new IllegalArgumentException(this+" "+c);
    if(c.signum()==0) return empty(val.size());
    IntConst a=rightmostOne(c);
    IntConst v0=val.divu(a);
    if(a.equals(c)) return valueOf(v0); 
    IntConst b=rightmostOne(c.sub(a).divu(a)); 
    IntConst v=propagateRight(v0.divu(b));
    return valueOf(v.mul(b).bor(v).bor(v0));
  }
  public IntLive inheritDivu0() {
    return valueOf(rightmostOne(val).neg());
  }
  public IntLive inheritDivu1() { return valueOf(val.size()); }
  public IntLive inheritDivu0(IntConst c1) {
    if(c1.size()!=val.size()) throw new IllegalArgumentException(this+" "+c1);
    IntConst a=rightmostOne(c1);
    if(a.equals(c1)) return valueOf(val.mul(a));
    IntConst b=IntConst.valueOf(c1.size(),0).bnot().divu(c1);
    if(val.band(propagateRight(b)).signum()==0) return empty(val.size());
    return valueOf(a.mul(rightmostOne(val)).neg());
  }
  public IntLive inheritDivu1(IntConst c0) {
    if(c0.size()!=val.size()) throw new IllegalArgumentException(this+" "+c0);
    return valueOf(val.size());
  }
  public IntLive inheritDivs0() { return allOrEmpty(val,val.size()); }
  public IntLive inheritDivs1() { return valueOf(val.size()); }
  public IntLive inheritDivs0(IntConst c1) {
    if(c1.size()!=val.size()) throw new IllegalArgumentException(this+" "+c1);
    if(c1.signum()==0) return empty(val.size());
    if(val.signum()==0) return this;
    final IntConst zero=IntConst.valueOf(c1.size(),0);
    final IntConst one=IntConst.valueOf(c1.size(),1);
    final IntConst msb=one.lsh(c1.size()-1);
    final IntConst all=zero.bnot();
    if(c1.equals(one)) return this;
    if(c1.equals(all)) return inheritNeg();
    IntConst c=c1.signum()>=0 ? c1 : c1.neg();
    IntConst a=rightmostOne(c);
    if(a.equals(c)) {
      IntConst v=propagateRight(val).mul(a).add(a).sub(one).bor(msb);
      if(c1.signum()<0 && val.band(all.divu(a)).signum()==0) {
        v=a.equals(msb) ? zero : v.band(a.neg());
      }
      return valueOf(v);
    }
    IntConst v=all;
    if(a.equals(one)) { 
      if(c1.signum()>0) {
        v=rightmostOne(c.sub(one)).neg();
        IntConst b=msb.divu(c); 
        if(val.band(propagateRight(b)).signum()!=0) v=v.bor(rightmostOne(val).neg());
      }
      if(val.equals(one) && c.add(msb.mods(c)).equals(one)) v=v.band(msb.bnot());
      return valueOf(v);
    }
    if(c1.signum()<0) { 
      IntConst b=msb.divu(c);
      if(val.band(propagateRight(b)).signum()==0) v=v.band(a.neg());
    }
    return valueOf(v);
  }
  public IntLive inheritDivs1(IntConst c0) { return inheritDivu1(c0); }
  public IntLive inheritModu0() { return allOrEmpty(val,val.size()); }
  public IntLive inheritModu1() { return valueOf(val.size()); }
  public IntLive inheritModu0(IntConst c1) {
    if(c1.size()!=val.size()) throw new IllegalArgumentException(this+" "+c1);
    if(c1.signum()==0) return empty(val.size());
    IntConst a=rightmostOne(c1);
    if(a.equals(c1)) return valueOf(val.band(a.sub(IntConst.valueOf(a.size(),1))));
    IntConst b=propagateRight(c1).band(a.neg());
    if(val.band(b).signum()==0) return valueOf(a.sub(IntConst.valueOf(a.size(),1)).band(val));
    return valueOf(a.neg().bor(val));
  }
  public IntLive inheritModu1(IntConst c0) { return inheritDivu1(c0); }
  public IntLive inheritMods0() { return inheritModu0(); }
  public IntLive inheritMods1() { return valueOf(val.size()); }
  public IntLive inheritMods0(IntConst c1) {
    if(c1.size()!=val.size()) throw new IllegalArgumentException(this+" "+c1);
    if(c1.signum()==0) return empty(val.size());
    final IntConst one=IntConst.valueOf(c1.size(),1);
    final IntConst msb=one.lsh(c1.size()-1);
    if(c1.signum()<0) c1=c1.neg();
    if(c1.equals(one)) return empty(c1.size());
    IntConst a=rightmostOne(c1);
    if(a.equals(c1)) {
      IntConst v=val.band(a.sub(one));
      if(val.band(a.neg()).signum()!=0) v=v.bor(a.sub(one)).bor(msb);
      return valueOf(v);
    }
    IntConst v=val;
    if(val.band(a.neg()).signum()!=0) v=v.bor(a.neg());
    if(val.equals(one) && a.equals(one) && c1.add(msb.mods(c1)).equals(one)) v=v.band(msb.bnot());
    if(val.band(c1.neg()).signum()!=0) v=v.bor(a.sub(one));
    return valueOf(v);
  }
  public IntLive inheritMods1(IntConst c0) { return inheritDivu1(c0); }
  public IntLive inheritBand() { return this; }
  public IntLive inheritBand(IntConst c) { return valueOf(val.band(c)); }
  public IntLive inheritBor() { return this; }
  public IntLive inheritBor(IntConst c) { return valueOf(val.band(c.bnot())); }
  public IntLive inheritBxor() { return this; }
  public IntLive inheritBxor(IntConst c) {
    if(c.size()!=val.size()) throw new IllegalArgumentException(this+" "+c);
    return this;
  }
  public IntLive inheritLsh0() { return inheritAdd(); }
  public IntLive inheritLsh1(int t) { return allOrEmpty(val,t); }
  public IntLive inheritLsh0(IntConst c1) { return valueOf(val.rshu(c1)); }
  public IntLive inheritLsh1(IntConst c0,int t) { return inheritShift1(SHIFT_LSH,c0,t); }
  public IntLive inheritRshu0() {
    return valueOf(rightmostOne(val).neg());
  }
  public IntLive inheritRshu1(int t) { return allOrEmpty(val,t); }
  public IntLive inheritRshu0(IntConst c1) { return valueOf(val.lsh(c1)); }
  public IntLive inheritRshu1(IntConst c0,int t) { return inheritShift1(SHIFT_RSHU,c0,t); }
  public IntLive inheritRshs0() { return inheritRshu0(); }
  public IntLive inheritRshs1(int t) { return allOrEmpty(val.band(msbOnly(t).bnot()),t); }
  public IntLive inheritRshs0(IntConst c1) {
    IntConst v=val.lsh(c1);
    if(!v.rshu(c1).equals(val)) v=v.bor(msbOnly(val.size()));
    return valueOf(v);
  }
  public IntLive inheritRshs1(IntConst c0,int t) { return inheritShift1(SHIFT_RSHS,c0,t); }
  private IntLive inheritShift1(Shift op,IntConst c0,int t) {
    final int size=val.size(),size2=size<<1;
    if(c0.size()!=size) throw new IllegalArgumentException(this+" "+c0);
    int v=0,s=0;
    for(int m=1;s<t && m!=0 && m-0x80000000<size2-0x80000000;m<<=1,s++) {
      IntConst a=IntConst.valueOf(size,0);
      for(int n=0;n<size;n=((n|m)+1)&~m) a=a.bor(op.eval(c0,n).bxor(op.eval(c0,n+m)));
      if(a.band(val).signum()!=0) v|=m;
    }
    return valueOf(IntConst.valueOf(s,v).convsx(t));
  }
  public IntLive inheritNeg() { return inheritAdd(); }
  public IntLive inheritBnot() { return this; }
  public IntLive inheritTsteq(int t) {
    return allOrEmpty(val.band(IntConst.valueOf(val.size(),1)),t);
  }
  public IntLive inheritTsteq(IntConst c) {
    return allOrEmpty(val.band(IntConst.valueOf(val.size(),1)),c.size());
  }
  public IntLive inheritTstne(int t) { return inheritTsteq(t); }
  public IntLive inheritTstne(IntConst c) { return inheritTsteq(c); }
  public IntLive inheritTstltu0(int t) { return inheritTsteq(t); }
  public IntLive inheritTstltu1(int t) { return inheritTsteq(t); }
  public IntLive inheritTstltu0(IntConst c1) {
    if(val.band(IntConst.valueOf(val.size(),1)).signum()==0) return empty(c1.size());
    return valueOf(rightmostOne(c1).neg());
  }
  public IntLive inheritTstltu1(IntConst c0) {
    if(val.band(IntConst.valueOf(val.size(),1)).signum()==0) return empty(c0.size());
    return valueOf(rightmostOne(c0.add(IntConst.valueOf(c0.size(),1))).neg());
  }
  public IntLive inheritTstgtu0(int t) { return inheritTsteq(t); }
  public IntLive inheritTstgtu1(int t) { return inheritTsteq(t); }
  public IntLive inheritTstgtu0(IntConst c1) { return inheritTstltu1(c1); }
  public IntLive inheritTstgtu1(IntConst c0) { return inheritTstltu0(c0); }
  public IntLive inheritTstleu0(int t) { return inheritTsteq(t); }
  public IntLive inheritTstleu1(int t) { return inheritTsteq(t); }
  public IntLive inheritTstleu0(IntConst c1) { return inheritTstltu1(c1); }
  public IntLive inheritTstleu1(IntConst c0) { return inheritTstltu0(c0); }
  public IntLive inheritTstgeu0(int t) { return inheritTsteq(t); }
  public IntLive inheritTstgeu1(int t) { return inheritTsteq(t); }
  public IntLive inheritTstgeu0(IntConst c1) { return inheritTstltu0(c1); }
  public IntLive inheritTstgeu1(IntConst c0) { return inheritTstltu1(c0); }
  public IntLive inheritTstlts0(int t) { return inheritTsteq(t); }
  public IntLive inheritTstlts1(int t) { return inheritTsteq(t); }
  public IntLive inheritTstlts0(IntConst c1) {
    if(val.band(IntConst.valueOf(val.size(),1)).signum()==0) return empty(c1.size());
    return valueOf(rightmostOne(c1.add(msbOnly(c1.size()))).neg());
  }
  public IntLive inheritTstlts1(IntConst c0) {
    if(val.band(IntConst.valueOf(val.size(),1)).signum()==0) return empty(c0.size());
    return valueOf(rightmostOne(c0.sub(msbOnly(c0.size()).bnot())).neg());
  }
  public IntLive inheritTstgts0(int t) { return inheritTsteq(t); }
  public IntLive inheritTstgts1(int t) { return inheritTsteq(t); }
  public IntLive inheritTstgts0(IntConst c1) { return inheritTstlts1(c1); }
  public IntLive inheritTstgts1(IntConst c0) { return inheritTstlts0(c0); }
  public IntLive inheritTstles0(int t) { return inheritTsteq(t); }
  public IntLive inheritTstles1(int t) { return inheritTsteq(t); }
  public IntLive inheritTstles0(IntConst c1) { return inheritTstlts1(c1); }
  public IntLive inheritTstles1(IntConst c0) { return inheritTstlts0(c0); }
  public IntLive inheritTstges0(int t) { return inheritTsteq(t); }
  public IntLive inheritTstges1(int t) { return inheritTsteq(t); }
  public IntLive inheritTstges0(IntConst c1) { return inheritTstlts0(c1); }
  public IntLive inheritTstges1(IntConst c0) { return inheritTstlts1(c0); }
  public IntLive inheritConvzx(int t) { return valueOf(val.convit(t)); }
  public IntLive inheritConvsx(int t) {
    IntConst v=val.convit(t);
    IntConst a=IntConst.valueOf(val.size(),1).lsh(t).neg();
    if(val.band(a).signum()!=0) v=v.bor(msbOnly(t));
    return valueOf(v);
  }
  public IntLive inheritConvit(int t) { return valueOf(val.convzx(t)); }
  public IntLive inheritIfthenelse0(int t) { return allOrEmpty(val,t); }
  public IntLive inheritIfthenelse1() { return this; }
  public IntLive inheritIfthenelse2() { return this; }
  public IntLive inheritIfthenelse0_1(int t,IntConst c1) { return inheritIfthenelse0(t); }
  public IntLive inheritIfthenelse0_2(int t,IntConst c2) { return inheritIfthenelse0(t); }
  public IntLive inheritIfthenelse1_0(IntConst c0) { return c0.signum()!=0 ? this : empty(val.size()); }
  public IntLive inheritIfthenelse1_2(IntConst c2) { return inheritIfthenelse1(); }
  public IntLive inheritIfthenelse2_0(IntConst c0) { return c0.signum()==0 ? this : empty(val.size()); }
  public IntLive inheritIfthenelse2_1(IntConst c1) { return inheritIfthenelse2(); }
  public IntLive inheritIfthenelse0(int t,IntConst c1,IntConst c2) {
    return allOrEmpty(c1.bxor(c2).band(val),t);
  }
  public IntLive inheritIfthenelse1(IntConst c0,IntConst c2) { return inheritIfthenelse1_0(c0); }
  public IntLive inheritIfthenelse2(IntConst c0,IntConst c1) { return inheritIfthenelse2_0(c0); }
  public IntConst intConstValue() { return val; }
  public boolean equals(Object o) {
    return o==this || o instanceof IntLive && val.equals((((IntLive)o).val));
  }
  public int hashCode() { return val.hashCode(); }
  public String toString() {
    StringBuffer sb=new StringBuffer("{");
    final IntConst one=IntConst.valueOf(val.size(),1);
    int j=-2;
    for(int i=0;i<val.size();i++) {
      int s=val.rshu(i).band(one).signum();
      if(j<0 && s>0) {
        if(j==-1) sb.append(',');
        sb.append(i);
        j=i; 
      }
      if(j>=0 && s==0) {
        if(i>j+1) sb.append("..").append(i-1);
        j=-1;
      }
    }
    if(j>=0 && j<val.size()-1) sb.append("..").append(val.size()-1);
    return sb.append("}:").append(val.size()).toString();
  }
  private static IntConst rightmostOne(IntConst c) { return c.neg().band(c); }
  private static IntConst propagateRight(IntConst c) {
    for(int i=1;i>=0 && i<c.size();i<<=1) c=c.bor(c.rshu(i));
    return c;
  }
  private static IntConst msbOnly(int t) { return IntConst.valueOf(t,1).lsh(t-1); }
  private static IntLive allOrEmpty(IntConst c,int t) {
    return c.signum()==0 ? empty(t) : valueOf(t);
  }

}
