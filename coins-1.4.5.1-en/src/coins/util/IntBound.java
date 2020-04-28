/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.util;

public final class IntBound {

// field

  public final IntConst lower;
  public final IntConst upper;

// constructor

  public IntBound(IntConst val) {
    this.lower=val; this.upper=val;
  }
  public IntBound(IntConst lower,IntConst upper) {
    if(lower.size()!=upper.size()) throw new IllegalArgumentException(lower+" "+upper);
    this.lower=lower; this.upper=upper;
  }

// method

  public int size() {
    return lower.size();
  }
  public boolean contains(IntConst c) {
    if(size()!=c.size()) throw new IllegalArgumentException(this+" "+c);
    return c.sub(lower).compareTo(upper.sub(lower))<=0;
  }
  public IntBound union(IntBound b) {
    if(size()!=b.size()) throw new IllegalArgumentException(this+" "+b);
    IntConst u0=upper.sub(lower);
    IntConst l1=b.lower.sub(lower);
    IntConst u1=b.upper.sub(lower);
    if(l1.compareTo(u1)<=0) { 
      if(u1.compareTo(u0)<=0) return this;
      if(l1.compareTo(u0)<=0) return new IntBound(lower,b.upper);
      if(u1.compareTo(u0.sub(l1))<=0) return new IntBound(lower,b.upper);
      else return new IntBound(b.lower,upper);
    } else {
      if(u1.compareTo(u0)>=0) return b;
      if(l1.compareTo(u0)>0) return new IntBound(b.lower,upper);
      IntConst l=IntConst.valueOf(size(),0);
      return new IntBound(l,l.bnot());
    }
  }
  public IntBound intersection(IntBound b) {
    if(size()!=b.size()) throw new IllegalArgumentException(this+" "+b);
    IntConst u0=upper.sub(lower);
    IntConst l1=b.lower.sub(lower);
    IntConst u1=b.upper.sub(lower);
    if(l1.compareTo(u1)<=0) { 
      if(u1.compareTo(u0)<=0) return b;
      if(l1.compareTo(u0)<=0) return new IntBound(b.lower,upper);
      return null;
    } else {
      if(u1.compareTo(u0)>=0) return this;
      if(l1.compareTo(u0)>0) return new IntBound(lower,b.upper);
      if(u0.compareTo(u1.sub(l1))<=0) return this;
      else return b;
    }
  }
  public IntBound add(IntBound b) {
    if(size()!=b.size()) throw new IllegalArgumentException(this+" "+b);
    IntConst r0=upper.sub(lower); 
    IntConst r1=b.upper.sub(b.lower); 
    IntConst l,u;
    if(r0.add(r1).compareTo(r0)<0) { l=IntConst.valueOf(size(),0); u=l.bnot(); }
    else { l=lower.add(b.lower); u=upper.add(b.upper); }
    return new IntBound(l,u);
  }
  public IntBound sub(IntBound b) {
    if(size()!=b.size()) throw new IllegalArgumentException(this+" "+b);
    IntConst r0=upper.sub(lower);
    IntConst r1=b.upper.sub(b.lower);
    IntConst l,u;
    if(r0.add(r1).compareTo(r0)<0) { l=IntConst.valueOf(size(),0); u=l.bnot(); }
    else { l=lower.sub(b.upper); u=upper.sub(b.lower); }
    return new IntBound(l,u);
  }
  public IntBound mul(IntBound b) {
    if(size()!=b.size()) throw new IllegalArgumentException(this+" "+b);
    final IntConst zero=IntConst.valueOf(size(),0);
    final IntConst msb=IntConst.valueOf(size(),1).lsh(size()-1);
    final IntBound plus=new IntBound(zero,msb.bnot()); 
    final IntBound minus=new IntBound(msb,zero.bnot()); 
    IntBound result=null;
    IntBound b0,b1,b2;
    if((b0=this.intersection(plus))!=null) {
      if((b1=b.intersection(plus))!=null) {
        result=mul1(b0,b1);
      }
      if((b1=b.intersection(minus))!=null) {
        b2=mul1(b0,b1.neg()).neg();
        result=result==null ? b2 : result.union(b2);
      }
    }
    if((b0=this.intersection(minus))!=null) {
      if((b1=b.intersection(plus))!=null) {
        b2=mul1(b0.neg(),b1).neg();
        result=result==null ? b2 : result.union(b2);
      }
      if((b1=b.intersection(minus))!=null) {
        b2=mul1(b0.neg(),b1.neg());
        result=result==null ? b2 : result.union(b2);
      }
    }
    //assert result!=null;
    return result;
  }
  private static IntBound mul1(IntBound b0,IntBound b1) {
    //assert b0.size()==b1.size();
    final int s=b0.size(),s2=s*2;
    final IntConst m=IntConst.valueOf(s2,1).lsh(s);
    IntConst l,u;
    if(b0.upper.convzx(s2).mul(b1.upper.convzx(s2))
      .sub(b0.lower.convzx(s2).mul(b1.lower.convzx(s2)))
      .compareTo(m)>=0) { l=IntConst.valueOf(s,0); u=l.bnot(); }
    else { l=b0.lower.mul(b1.lower); u=b0.upper.mul(b1.upper); }
    return new IntBound(l,u);
  }
  public IntBound divu(IntBound b) {
    if(size()!=b.size()) throw new IllegalArgumentException(this+" "+b);
    IntConst l0=lower,u0=upper;
    IntConst l1=b.lower,u1=b.upper;
    if(l0.compareTo(u0)>0) { l0=IntConst.valueOf(size(),0); u0=l0.bnot(); }
    if(l1.compareTo(u1)>0) { l1=IntConst.valueOf(size(),0); u1=l1.bnot(); }
    if(l1.signum()==0) l1=IntConst.valueOf(size(),1);
    return new IntBound(l0.divu(u1),u0.divu(l1));
  }
  public IntBound divs(IntBound b) {
    if(size()!=b.size()) throw new IllegalArgumentException(this+" "+b);
    if(b.lower.signum()==0 && b.upper.signum()==0) throw new ArithmeticException(this+" "+b);
    final IntConst zero=IntConst.valueOf(size(),0);
    final IntConst msb=IntConst.valueOf(size(),1).lsh(size()-1);
    final IntBound plus=new IntBound(zero,msb.bnot());
    final IntBound minus=new IntBound(msb,zero.bnot());
    IntBound result=null;
    IntBound b0,b1,b2;
    if((b0=this.intersection(plus))!=null) {
      if((b1=b.intersection(plus))!=null) {
        result=b0.divu(b1);
      }
      if((b1=b.intersection(minus))!=null) {
        b2=b0.divu(b1.neg()).neg();
        result=result==null ? b2 : result.union(b2);
      }
    }
    if((b0=this.intersection(minus))!=null) {
      if((b1=b.intersection(plus))!=null) {
        b2=b0.neg().divu(b1).neg();
        result=result==null ? b2 : result.union(b2);
      }
      if((b1=b.intersection(minus))!=null) {
        b2=b0.neg().divu(b1.neg());
        result=result==null ? b2 : result.union(b2);
      }
    }
    //assert result!=null;
    return result;
  }
  public IntBound modu(IntBound b) {
    if(size()!=b.size()) throw new IllegalArgumentException(this+" "+b);
    if(b.lower.equals(b.upper)) {
      if(b.lower.signum()==0) throw new ArithmeticException(this+" "+b);
      if(lower.compareTo(upper)<=0 && lower.divu(b.lower).equals(upper.divu(b.lower))) {
        return new IntBound(lower.modu(b.lower),upper.modu(b.lower));
      }
    }
    IntConst l=IntConst.valueOf(size(),0);
    IntConst u=b.lower.compareTo(b.upper)<=0 ? b.upper.sub(IntConst.valueOf(size(),1)) : l.bnot();
    return new IntBound(l,u);
  }
  public IntBound mods(IntBound b) {
    if(size()!=b.size()) throw new IllegalArgumentException(this+" "+b);
    if(b.lower.signum()==0 && b.upper.signum()==0) throw new ArithmeticException(this+" "+b);
    final IntConst zero=IntConst.valueOf(size(),0);
    final IntConst msb=IntConst.valueOf(size(),1).lsh(size()-1);
    final IntBound plus=new IntBound(zero,msb.bnot());
    final IntBound minus=new IntBound(msb,zero.bnot());
    IntBound result=null;
    IntBound b0,b1,b2;
    if((b0=this.intersection(plus))!=null) {
      if((b1=b.intersection(plus))!=null) {
        result=b0.modu(b1);
      }
      if((b1=b.intersection(minus))!=null) {
        b2=b0.modu(b1.neg());
        result=result==null ? b2 : result.union(b2);
      }
    }
    if((b0=this.intersection(minus))!=null) {
      if((b1=b.intersection(plus))!=null) {
        b2=b0.neg().modu(b1).neg();
        result=result==null ? b2 : result.union(b2);
      }
      if((b1=b.intersection(minus))!=null) {
        b2=b0.neg().modu(b1.neg()).neg();
        result=result==null ? b2 : result.union(b2);
      }
    }
    //assert result!=null;
    return result;
  }
  public IntBound band(IntBound b) {
    if(size()!=b.size()) throw new IllegalArgumentException(this+" "+b);
    if(lower.compareTo(upper)<=0) {
      if(b.lower.compareTo(b.upper)<=0) {
        return minMaxAnd(lower,upper,b.lower,b.upper);
      } else {
        IntConst c0=IntConst.valueOf(size(),0),c1=c0.bnot();
        return minMaxAnd(lower,upper,c0,b.upper).union(minMaxAnd(lower,upper,b.lower,c1));
      }
    } else {
      if(b.lower.compareTo(b.upper)<=0) {
        IntConst c0=IntConst.valueOf(size(),0),c1=c0.bnot();
        return minMaxAnd(c0,upper,b.lower,b.upper).union(minMaxAnd(lower,c1,b.lower,b.upper));
      } else {
        IntConst c0=IntConst.valueOf(size(),0),c1=c0.bnot();
        return minMaxAnd(c0,upper,c0,b.upper).union(minMaxAnd(c0,upper,b.lower,c1))
               .union(minMaxAnd(lower,c1,c0,b.upper)).union(minMaxAnd(lower,c1,b.lower,c1));
      }
    }
  }
  private static IntBound minMaxAnd(IntConst a,IntConst b,IntConst c,IntConst d) {
    return new IntBound(minAnd(a,b,c,d),maxAnd(a,b,c,d));
  }
  private static IntConst minAnd(IntConst a,IntConst b,IntConst c,IntConst d) {
    final int size=a.size();
    IntConst m=IntConst.valueOf(size,1).lsh(size-1);
    while(m.signum()!=0) {
      if(a.bor(c).bnot().band(m).signum()!=0) {
        IntConst t;
        t=a.bor(m).band(m.neg());
        if(t.compareTo(b)<=0) { a=t; break; }
        t=c.bor(m).band(m.neg());
        if(t.compareTo(d)<=0) { c=t; break; }
      }
      m=m.rshu(1);
    }
    return a.band(c);
  }
  private static IntConst maxAnd(IntConst a,IntConst b,IntConst c,IntConst d) {
    final int size=a.size();
    IntConst m=IntConst.valueOf(size,1).lsh(size-1);
    final IntConst one=IntConst.valueOf(size,1);
    while(m.signum()!=0) {
      if(b.band(d.bnot()).band(m).signum()!=0) {
        IntConst t=b.band(m.bnot()).bor(m.sub(one));
        if(t.compareTo(a)>=0) { b=t; break; }
      } else if(b.bnot().band(d).band(m).signum()!=0) {
        IntConst t=d.band(m.bnot()).bor(m.sub(one));
        if(t.compareTo(c)<=0) { d=t; break; }
      }
      m=m.rshu(1);
    }
    return b.band(d);
  }
  public IntBound bor(IntBound b) {
    return this.bnot().band(b.bnot()).bnot();
  }
  public IntBound bxor(IntBound b) {
    if(size()!=b.size()) throw new IllegalArgumentException(this+" "+b);
    if(lower.compareTo(upper)<=0) {
      if(b.lower.compareTo(b.upper)<=0) {
        return minMaxXor(lower,upper,b.lower,b.upper);
      } else {
        IntConst c0=IntConst.valueOf(size(),0),c1=c0.bnot();
        return minMaxXor(lower,upper,c0,b.upper).union(minMaxXor(lower,upper,b.lower,c1));
      }
    } else {
      if(b.lower.compareTo(b.upper)<=0) {
        IntConst c0=IntConst.valueOf(size(),0),c1=c0.bnot();
        return minMaxXor(c0,upper,b.lower,b.upper).union(minMaxXor(lower,c1,b.lower,b.upper));
      } else {
        IntConst c0=IntConst.valueOf(size(),0),c1=c0.bnot();
        return minMaxXor(c0,upper,c0,b.upper).union(minMaxXor(c0,upper,b.lower,c1))
               .union(minMaxXor(upper,c1,c0,b.upper)).union(minMaxXor(upper,c1,b.lower,c1));
      }
    }
  }
  private static IntBound minMaxXor(IntConst a,IntConst b,IntConst c,IntConst d) {
    return new IntBound(minXor(a,b,c,d),maxXor(a,b,c,d));
  }
  private static IntConst minXor(IntConst a,IntConst b,IntConst c,IntConst d) {
    return minAnd(a,b,d.bnot(),c.bnot()).bor(minAnd(b.bnot(),a.bnot(),c,d));
  }
  private static IntConst maxXor(IntConst a,IntConst b,IntConst c,IntConst d) {
    final IntConst m=IntConst.valueOf(a.size(),0).bnot();
    return minAnd(maxAnd(a,b,d.bnot(),c.bnot()).bnot(),m,
                  maxAnd(b.bnot(),a.bnot(),c,d).bnot(),m).bnot();
  }
  public IntBound lsh(IntBound b) {
    b=saturate(b,size());
    IntBound result=null;
    for(int i=0;i<=size();i++) if(b.contains(IntConst.valueOf(b.size(),i))) {
      IntBound b1=this.lsh(i);
      result=result==null ? b1 : result.union(b1);
    }
    return result;
  }
  public IntBound rshu(IntBound b) {
    b=saturate(b,size());
    IntBound result=null;
    for(int i=0;i<=size();i++) if(b.contains(IntConst.valueOf(b.size(),i))) {
      IntBound b1=this.rshu(i);
      result=result==null ? b1 : result.union(b1);
    }
    return result;
  }
  public IntBound rshs(IntBound b) {
    b=saturate(b,size());
    IntBound result=null;
    for(int i=0;i<=size();i++) if(b.contains(IntConst.valueOf(b.size(),i))) {
      IntBound b1=this.rshs(i);
      result=result==null ? b1 : result.union(b1);
    }
    return result;
  }
  private static IntBound saturate(IntBound b,int i) {
    IntConst i1=IntConst.valueOf(b.size(),i);
    IntConst l=b.lower,u=b.upper;
    int cmp=l.compareTo(u);
    if(l.compareTo(i1)>=0) l=i1;
    if(u.compareTo(i1)>=0) {
      u=i1;
      if(cmp>0) l=IntConst.valueOf(b.size(),0); 
    }
    return new IntBound(l,u);
  }
  public IntBound lsh(int n) {
    if(n<0) throw new IllegalArgumentException(String.valueOf(n));
    if(n==0) return this;
    if(n>=size()) return new IntBound(IntConst.valueOf(size(),0));
    IntConst r=upper.sub(lower);
    IntConst l,u;
    if(r.compareTo(IntConst.valueOf(size(),1).lsh(size()-n))>=0) {
      l=IntConst.valueOf(size(),0); u=l.bnot();
    } else {
      l=lower.lsh(n); u=upper.lsh(n);
    }
    return new IntBound(l,u);
  }
  public IntBound rshu(int n) {
    if(n<0) throw new IllegalArgumentException(String.valueOf(n));
    if(n==0) return this;
    IntConst l=lower,u=upper;
    if(l.compareTo(u)>0) { l=IntConst.valueOf(size(),0); u=l.bnot(); }
    return new IntBound(l.rshu(n),u.rshu(n));
  }
  public IntBound rshs(int n) {
    if(n<0) throw new IllegalArgumentException(String.valueOf(n));
    if(n==0) return this;
    IntConst l=lower,u=upper;
    if(l.signedCompareTo(u)>0) { l=IntConst.valueOf(size(),1).lsh(size()-1); u=l.bnot(); }
    return new IntBound(l.rshs(n),u.rshs(n));
  }
  public IntBound neg() {
    return new IntBound(upper.neg(),lower.neg());
  }
  public IntBound bnot() {
    return new IntBound(upper.bnot(),lower.bnot());
  }
  public IntBound tsteq(IntBound b,int s) { return cmpeq(this,b,s,1); }
  public IntBound tstne(IntBound b,int s) { return cmpeq(this,b,s,0); }
  public IntBound tstltu(IntBound b,int s) { return cmpu(this,b,s,1); }
  public IntBound tstgtu(IntBound b,int s) { return cmpu(b,this,s,1); }
  public IntBound tstleu(IntBound b,int s) { return cmpu(b,this,s,0); }
  public IntBound tstgeu(IntBound b,int s) { return cmpu(this,b,s,0); }
  public IntBound tstlts(IntBound b,int s) { return cmps(this,b,s,1); }
  public IntBound tstgts(IntBound b,int s) { return cmps(b,this,s,1); }
  public IntBound tstles(IntBound b,int s) { return cmps(b,this,s,0); }
  public IntBound tstges(IntBound b,int s) { return cmps(this,b,s,0); }
  private static IntBound cmpeq(IntBound b0,IntBound b1,int s,int eq) {
    if(b0.size()!=b1.size()) throw new IllegalArgumentException(b0+" "+b1);
    if(b0.lower.equals(b0.upper) && b1.lower.equals(b1.upper) &&
       b0.lower.equals(b1.lower)) return new IntBound(IntConst.valueOf(s,eq));
    if(b0.intersection(b1)==null) return new IntBound(IntConst.valueOf(s,1-eq));
    return new IntBound(IntConst.valueOf(s,0),IntConst.valueOf(s,1));
  }
  private static IntBound cmpu(IntBound b0,IntBound b1,int s,int lt) {
    if(b0.size()!=b1.size()) throw new IllegalArgumentException(b0+" "+b1);
    if(b0.lower.compareTo(b0.upper)<=0 && b1.lower.compareTo(b1.upper)<=0) {
      if(b0.upper.compareTo(b1.lower)<0) return new IntBound(IntConst.valueOf(s,lt));
      if(b0.lower.compareTo(b1.upper)>=0) return new IntBound(IntConst.valueOf(s,1-lt));
    }
    return new IntBound(IntConst.valueOf(s,0),IntConst.valueOf(s,1));
  }
  private static IntBound cmps(IntBound b0,IntBound b1,int s,int lt) {
    if(b0.size()!=b1.size()) throw new IllegalArgumentException(b0+" "+b1);
    if(b0.lower.signedCompareTo(b0.upper)<=0 && b1.lower.signedCompareTo(b1.upper)<=0) {
      if(b0.upper.signedCompareTo(b1.lower)<0) return new IntBound(IntConst.valueOf(s,lt));
      if(b0.lower.signedCompareTo(b1.upper)>=0) return new IntBound(IntConst.valueOf(s,1-lt));
    }
    return new IntBound(IntConst.valueOf(s,0),IntConst.valueOf(s,1));
  }
  public IntBound convzx(int s) {
    if(s==size()) return this;
    if(s<size()) throw new IllegalArgumentException(this+" "+s);
    IntConst l=lower,u=upper;
    if(l.compareTo(u)>0) { l=IntConst.valueOf(size(),0); u=l.bnot(); }
    return new IntBound(l.convzx(s),u.convzx(s));
  }
  public IntBound convsx(int s) {
    if(s==size()) return this;
    if(s<size()) throw new IllegalArgumentException(this+" "+s);
    IntConst l=lower,u=upper;
    if(l.signedCompareTo(u)>0) { l=IntConst.valueOf(size(),1).lsh(size()-1); u=l.bnot(); }
    return new IntBound(l.convsx(s),u.convsx(s));
  }
  public IntBound convit(int s) {
    if(s==size()) return this;
    if(s>size() || s<=0) throw new IllegalArgumentException(this+" "+s);
    IntConst r=upper.sub(lower);
    IntConst l,u;
    if(r.compareTo(IntConst.valueOf(size(),1).lsh(s))>=0) {
      l=IntConst.valueOf(s,0); u=l.bnot();
    } else {
      l=lower.convit(s); u=upper.convit(s);
    }
    return new IntBound(l,u);
  }
  public IntBound ifthenelse(IntBound t,IntBound f) {
    if(t.size()!=f.size()) throw new IllegalArgumentException(this+" "+t+' '+f);
    if(lower.signum()==0 && lower.equals(upper)) return t;
    if(!this.contains(IntConst.valueOf(size(),0))) return f;
    return t.union(f);
  }
  public boolean equals(Object o) {
    return o==this ||
           o instanceof IntBound &&
           lower.equals(((IntBound)o).lower) && upper.equals(((IntBound)o).upper);
  }
  public int hashCode() {
    return lower.hashCode()*37+upper.hashCode();
  }
  public String toString() {
    return "("+lower.bigValue()+".."+upper.bigValue()+"):"+size();
  }

}
