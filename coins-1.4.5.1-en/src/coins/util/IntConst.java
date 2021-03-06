/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.util;

import java.math.BigInteger;

public abstract class IntConst implements Comparable {

// field

  /*private*/ final int size;

// static field

  public static final IntConst I8_M1=L.I8_M1;
  public static final IntConst I8_0=L.I8_0;
  public static final IntConst I8_1=L.I8_1;
  public static final IntConst I8_2=L.I8_2;
  public static final IntConst I16_M1=L.I16_M1;
  public static final IntConst I16_0=L.I16_0;
  public static final IntConst I16_1=L.I16_1;
  public static final IntConst I16_2=L.I16_2;
  public static final IntConst I32_M1=L.I32_M1;
  public static final IntConst I32_0=L.I32_0;
  public static final IntConst I32_1=L.I32_1;
  public static final IntConst I32_2=L.I32_2;
  private static final BigInteger BIG_LONG_MASK=bigMask(64);

// member type

  private static class L extends IntConst {
    private long l;
    static final L I8_M1=new L(8,0xFFL);
    static final L I8_0=new L(8,0);
    static final L I8_1=new L(8,1);
    static final L I8_2=new L(8,2);
    static final L I16_M1=new L(16,0xFFFFL);
    static final L I16_0=new L(16,0);
    static final L I16_1=new L(16,1);
    static final L I16_2=new L(16,2);
    static final L I32_M1=new L(32,0xFFFFFFFFL);
    static final L I32_0=new L(32,0);
    static final L I32_1=new L(32,1);
    static final L I32_2=new L(32,2);
    private static final L[] I8_CONST={I8_M1,I8_0,I8_1,I8_2};
    private static final L[] I16_CONST={I16_M1,I16_0,I16_1,I16_2};
    private static final L[] I32_CONST={I32_M1,I32_0,I32_1,I32_2};
    private static final long MSB=0x8000000000000000L;
    private L(int size,long val) { super(size); l=val; }
    static L valueOfL(int size,long val) {
      if(val>=-1 && val<=2) {
        if(size==8) return I8_CONST[(int)(val+1)];
        if(size==16) return I16_CONST[(int)(val+1)];
        if(size==32) return I32_CONST[(int)(val+1)];
      }
      return new L(size,val&longMask(size));
    }
    public IntConst add(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(size,l+((L)c).l);
    }
    public IntConst sub(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(size,l-((L)c).l);
    }
    public IntConst mul(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(size,l*((L)c).l);
    }
    public IntConst divu(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      long x=l,y=((L)c).l;
      if(x>=0 && y>=0) return valueOfL(size,x/y);
      BigInteger x1=BigInteger.valueOf(x).and(BIG_LONG_MASK);
      BigInteger y1=BigInteger.valueOf(y).and(BIG_LONG_MASK);
      return valueOfL(size,x1.divide(y1).longValue());
    }
    public IntConst divs(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(size,signedLongValue()/c.signedLongValue());
    }
    public IntConst modu(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      long x=l,y=((L)c).l;
      if(x>=0 && y>=0) return valueOfL(size,x%y);
      BigInteger x1=BigInteger.valueOf(x).and(BIG_LONG_MASK);
      BigInteger y1=BigInteger.valueOf(y).and(BIG_LONG_MASK);
      return valueOfL(size,x1.remainder(y1).longValue());
    }
    public IntConst mods(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(size,signedLongValue()%c.signedLongValue());
    }
    public IntConst band(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(size,l&((L)c).l);
    }
    public IntConst bor(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(size,l|((L)c).l);
    }
    public IntConst bxor(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(size,l^((L)c).l);
    }
    public IntConst lsh(IntConst c) { return lsh(c.count(size)); }
    public IntConst rshu(IntConst c) { return rshu(c.count(size)); }
    public IntConst rshs(IntConst c) { return rshs(c.count(size)); }
    public IntConst lsh(int n) {
      if(n<0) throw new IllegalArgumentException(String.valueOf(n));
      return valueOfL(size,n<size ? l<<n : 0);
    }
    public IntConst rshu(int n) {
      if(n<0) throw new IllegalArgumentException(String.valueOf(n));
      return valueOfL(size,n<size ? l>>>n : 0);
    }
    public IntConst rshs(int n) {
      if(n<0) throw new IllegalArgumentException(String.valueOf(n));
      if(n>=size) n=size-1;
      return valueOfL(size,l<<(64-size)>>(64-size+n));
    }
    public IntConst neg() { return valueOfL(size,-l); }
    public IntConst bnot() { return valueOfL(size,~l); }
    public IntConst tsteq(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(s,l==((L)c).l ? 1 : 0);
    }
    public IntConst tstne(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(s,l!=((L)c).l ? 1 : 0);
    }
    public IntConst tstltu(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(s,(l^MSB)<(((L)c).l^MSB) ? 1 : 0);
    }
    public IntConst tstgtu(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(s,(l^MSB)>(((L)c).l^MSB) ? 1 : 0);
    }
    public IntConst tstleu(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(s,(l^MSB)<=(((L)c).l^MSB) ? 1 : 0);
    }
    public IntConst tstgeu(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(s,(l^MSB)>=(((L)c).l^MSB) ? 1 : 0);
    }
    public IntConst tstlts(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(s,signedLongValue()<c.signedLongValue() ? 1 : 0);
    }
    public IntConst tstgts(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(s,signedLongValue()>c.signedLongValue() ? 1 : 0);
    }
    public IntConst tstles(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(s,signedLongValue()<=c.signedLongValue() ? 1 : 0);
    }
    public IntConst tstges(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfL(s,signedLongValue()>=c.signedLongValue() ? 1 : 0);
    }
    public IntConst convzx(int s) {
      if(s<size) throw new IllegalArgumentException(this+" "+s);
      return valueOf(s,l);
    }
    public IntConst convsx(int s) {
      if(s<size) throw new IllegalArgumentException(this+" "+s);
      if(s<=64) return valueOfL(s,signedLongValue());
      return valueOf(s,signedBigValue());
    }
    public IntConst convit(int s) {
      if(s>size || s<=0) throw new IllegalArgumentException(this+" "+s);
      return valueOfL(s,l);
    }
    public FloatConst convuf(int msize,int esize) {
      if(l>=0) return FloatConst.valueOf(msize,esize,l);
      return FloatConst.valueOf(msize,esize,BigInteger.valueOf(l).and(BIG_LONG_MASK));
    }
    public FloatConst convsf(int msize,int esize) {
      return FloatConst.valueOf(msize,esize,signedLongValue());
    }
    public IntConst ifthenelse(IntConst t,IntConst f) {
      if(t.size!=f.size) throw new IllegalArgumentException(this+" "+t+' '+f);
      return l!=0 ? t : f;
    }
    public FloatConst ifthenelse(FloatConst t,FloatConst f) {
      if(t.msize()!=f.msize() || t.esize()!=f.esize()) throw new IllegalArgumentException(this+" "+t+' '+f);
      return l!=0 ? t : f;
    }
    public long longValue() { return l; }
    public long signedLongValue() { return l<<(64-size)>>(64-size); }
    public BigInteger bigValue() { return BigInteger.valueOf(l).and(BIG_LONG_MASK); }
    public BigInteger signedBigValue() { return BigInteger.valueOf(signedLongValue()); }
    public int compareTo(Object o) {
      IntConst c=(IntConst)o;
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return l==((L)c).l ? 0 : (l^MSB)<(((L)c).l^MSB) ? -1 : 1;
    }
    public int signedCompareTo(Object o) {
      IntConst c=(IntConst)o;
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return l==((L)c).l ? 0 : signedLongValue()<c.signedLongValue() ? -1 : 1;
    }
    public int signum() { return l==0 ? 0 : (l<<(64-size))<0 ? -1 : 1; }
    public boolean equals(Object o) {
      return o==this || o instanceof L && size==((L)o).size && l==((L)o).l;
    }
    public int hashCode() { return size*37+(int)((l>>>32)^l); }
    public String toString(int radix) {
      if(radix==10 && size<64) return String.valueOf(l);
      return bigValue().toString(radix);
    }
    public String toSignedString(int radix) {
      if(radix==10) return String.valueOf(l);
      return signedBigValue().toString(radix);
    }
    /*private*/ int count(int size) { return l>=0 || l<size ? (int)l : size; }
  }

  private static class B extends IntConst {
    private BigInteger b;
    private B(int size,BigInteger val) { super(size); b=val; }
    static B valueOfB(int size,BigInteger val) { return new B(size,val.and(bigMask(size))); }
    public IntConst add(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfB(size,b.add(((B)c).b));
    }
    public IntConst sub(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfB(size,b.subtract(((B)c).b));
    }
    public IntConst mul(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfB(size,b.multiply(((B)c).b));
    }
    public IntConst divu(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfB(size,b.divide(((B)c).b));
    }
    public IntConst divs(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfB(size,signedBigValue().divide(c.signedBigValue()));
    }
    public IntConst modu(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfB(size,b.remainder(((B)c).b));
    }
    public IntConst mods(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfB(size,signedBigValue().remainder(c.signedBigValue()));
    }
    public IntConst band(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfB(size,b.and(((B)c).b));
    }
    public IntConst bor(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfB(size,b.or(((B)c).b));
    }
    public IntConst bxor(IntConst c) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOfB(size,b.xor(((B)c).b));
    }
    public IntConst lsh(IntConst c) { return lsh(c.count(size)); }
    public IntConst rshu(IntConst c) { return rshu(c.count(size)); }
    public IntConst rshs(IntConst c) { return rshs(c.count(size)); }
    public IntConst lsh(int n) {
      if(n<0) throw new IllegalArgumentException(String.valueOf(n));
      return valueOfB(size,n<size ? b.shiftLeft(n) : BigInteger.ZERO);
    }
    public IntConst rshu(int n) {
      if(n<0) throw new IllegalArgumentException(String.valueOf(n));
      return valueOfB(size,b.shiftRight(n));
    }
    public IntConst rshs(int n) {
      if(n<0) throw new IllegalArgumentException(String.valueOf(n));
      return valueOfB(size,signedBigValue().shiftRight(n));
    }
    public IntConst neg() { return valueOfB(size,b.negate()); }
    public IntConst bnot() { return valueOfB(size,b.not()); }
    public IntConst tsteq(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOf(s,b.equals(((B)c).b) ? 1 : 0);
    }
    public IntConst tstne(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOf(s,!b.equals(((B)c).b) ? 1 : 0);
    }
    public IntConst tstltu(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOf(s,b.compareTo(((B)c).b)<0 ? 1 : 0);
    }
    public IntConst tstgtu(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOf(s,b.compareTo(((B)c).b)>0 ? 1 : 0);
    }
    public IntConst tstleu(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOf(s,b.compareTo(((B)c).b)<=0 ? 1 : 0);
    }
    public IntConst tstgeu(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOf(s,b.compareTo(((B)c).b)>=0 ? 1 : 0);
    }
    public IntConst tstlts(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOf(s,signedBigValue().compareTo(c.signedBigValue())<0 ? 1 : 0);
    }
    public IntConst tstgts(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOf(s,signedBigValue().compareTo(c.signedBigValue())>0 ? 1 : 0);
    }
    public IntConst tstles(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOf(s,signedBigValue().compareTo(c.signedBigValue())<=0 ? 1 : 0);
    }
    public IntConst tstges(IntConst c,int s) {
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return valueOf(s,signedBigValue().compareTo(c.signedBigValue())>=0 ? 1 : 0);
    }
    public IntConst convzx(int s) {
      if(s<size) throw new IllegalArgumentException(this+" "+s);
      return valueOfB(s,b);
    }
    public IntConst convsx(int s) {
      if(s<size) throw new IllegalArgumentException(this+" "+s);
      return valueOfB(s,signedBigValue());
    }
    public IntConst convit(int s) {
      if(s>size || s<=0) throw new IllegalArgumentException(this+" "+s);
      return valueOf(s,b);
    }
    public FloatConst convuf(int msize,int esize) {
      return FloatConst.valueOf(msize,esize,b);
    }
    public FloatConst convsf(int msize,int esize) {
      return FloatConst.valueOf(msize,esize,signedBigValue());
    }
    public IntConst ifthenelse(IntConst t,IntConst f) {
      if(t.size!=f.size) throw new IllegalArgumentException(this+" "+t+' '+f);
      return b.signum()!=0 ? t : f;
    }
    public FloatConst ifthenelse(FloatConst t,FloatConst f) {
      if(t.msize()!=f.msize() || t.esize()!=f.esize()) throw new IllegalArgumentException(this+" "+t+' '+f);
      return b.signum()!=0 ? t : f;
    }
    public long longValue() { return b.longValue(); }
    public long signedLongValue() { return b.longValue(); }
    public BigInteger bigValue() { return b; }
    public BigInteger signedBigValue() {
      return b.testBit(size-1) ? b.subtract(BigInteger.ONE.shiftLeft(size)) : b;
    }
    public int compareTo(Object o) {
      IntConst c=(IntConst)o;
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return b.compareTo(((B)c).b);
    }
    public int signedCompareTo(Object o) {
      IntConst c=(IntConst)o;
      if(c.size!=size) throw new IllegalArgumentException(this+" "+c);
      return signedBigValue().compareTo(c.signedBigValue());
    }
    public int signum() { return b.signum()==0 ? 0 : b.testBit(size-1) ? -1 : 1; }
    public boolean equals(Object o) {
      return o==this || o instanceof B && size==((B)o).size && b.equals(((B)o).b);
    }
    public int hashCode() { return size*37+b.hashCode(); }
    public String toString(int radix) { return b.toString(radix); }
    public String toSignedString(int radix) { return signedBigValue().toString(radix); }
    /*private*/ int count(int size) {
      return b.compareTo(BigInteger.valueOf(size))<0 ? (int)b.longValue() : size;
    }
  }

// constructor

  private IntConst(int size) {
    this.size=size;
  }

// factory method

  public static IntConst valueOf(int size,long val) {
    if(size<=0) throw new IllegalArgumentException(String.valueOf(size));
    if(size<=64) return L.valueOfL(size,val);
    return B.valueOfB(size,BigInteger.valueOf(val).and(BIG_LONG_MASK));
  }
  public static IntConst valueOf(int size,BigInteger val) {
    if(size<=0) throw new IllegalArgumentException(String.valueOf(size));
    if(size<=64) return L.valueOfL(size,val.longValue());
    if(val.getClass()!=BigInteger.class) val=new BigInteger(val.toByteArray());
    return B.valueOfB(size,val);
  }

// method

  public int size() {
    return size;
  }
  public abstract IntConst add(IntConst c);
  public abstract IntConst sub(IntConst c);
  public abstract IntConst mul(IntConst c);
  public abstract IntConst divu(IntConst c);
  public abstract IntConst divs(IntConst c);
  public abstract IntConst modu(IntConst c);
  public abstract IntConst mods(IntConst c);
  public abstract IntConst band(IntConst c);
  public abstract IntConst bor(IntConst c);
  public abstract IntConst bxor(IntConst c);
  public abstract IntConst lsh(IntConst c);
  public abstract IntConst rshu(IntConst c);
  public abstract IntConst rshs(IntConst c);
  public abstract IntConst lsh(int n);
  public abstract IntConst rshu(int n);
  public abstract IntConst rshs(int n);
  public abstract IntConst neg();
  public abstract IntConst bnot();
  public abstract IntConst tsteq(IntConst c,int s);
  public abstract IntConst tstne(IntConst c,int s);
  public abstract IntConst tstltu(IntConst c,int s);
  public abstract IntConst tstgtu(IntConst c,int s);
  public abstract IntConst tstleu(IntConst c,int s);
  public abstract IntConst tstgeu(IntConst c,int s);
  public abstract IntConst tstlts(IntConst c,int s);
  public abstract IntConst tstgts(IntConst c,int s);
  public abstract IntConst tstles(IntConst c,int s);
  public abstract IntConst tstges(IntConst c,int s);
  public abstract IntConst convzx(int s);
  public abstract IntConst convsx(int s);
  public abstract IntConst convit(int s);
  public abstract FloatConst convuf(int msize,int esize);
  public abstract FloatConst convsf(int msize,int esize);
  public abstract IntConst ifthenelse(IntConst t,IntConst f);
  public abstract FloatConst ifthenelse(FloatConst t,FloatConst f);
//  public int intValue() {
//  public int signedIntValue() {
  public abstract long longValue();
  public abstract long signedLongValue();
  public abstract BigInteger bigValue();
  public abstract BigInteger signedBigValue();
  //public float floatValue() {
  //public float signedFloatValue() {
  //public double doubleValue() {
  //public double signedDoubleValue() {
  public abstract int compareTo(Object o);
  public abstract int signedCompareTo(Object o);
  public abstract int signum();
  public abstract boolean equals(Object o);
  public abstract int hashCode();
  public String toString() {
    return "(IntConst I"+size+' '+toString(10)+')';
  }
  public abstract String toString(int radix);
  public abstract String toSignedString(int radix);
  /*private*/ abstract int count(int size);
  private static long longMask(int size) {
    return size==64 ? -1 : (1L<<size)-1;
  }
  private static BigInteger bigMask(int size) {
    return BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE);
  }

}
