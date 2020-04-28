int printf(char *s, ...);

char s3[]="%d %d %d\n";
char s8[]="%d %d %d %d %d %d %d %d\n";

int a00=-3.402823466e+38F>=-3.402823466e+38F,a01=-3.402823466e+38F>=-2.7F,
    a02=-3.402823466e+38F>=-1.175494351e-38F,a03=-3.402823466e+38F>=-0.0F,
    a04=-3.402823466e+38F>=0.0F,a05=-3.402823466e+38F>=1.175494351e-38F,
    a06=-3.402823466e+38F>=2.7F,a07=-3.402823466e+38F>=3.402823466e+38F;
int a10=            -2.7F>=-3.402823466e+38F,a11=            -2.7F>=-2.7F,
    a12=            -2.7F>=-1.175494351e-38F,a13=            -2.7F>=-0.0F,
    a14=            -2.7F>=0.0F,a15=            -2.7F>=1.175494351e-38F,
    a16=            -2.7F>=2.7F,a17=            -2.7F>=3.402823466e+38F;
int a20=-1.175494351e-38F>=-3.402823466e+38F,a21=-1.175494351e-38F>=-2.7F,
    a22=-1.175494351e-38F>=-1.175494351e-38F,a23=-1.175494351e-38F>=-0.0F,
    a24=-1.175494351e-38F>=0.0F,a25=-1.175494351e-38F>=1.175494351e-38F,
    a26=-1.175494351e-38F>=2.7F,a27=-1.175494351e-38F>=3.402823466e+38F;
int a30=            -0.0F>=-3.402823466e+38F,a31=            -0.0F>=-2.7F,
    a32=            -0.0F>=-1.175494351e-38F,a33=            -0.0F>=-0.0F,
    a34=            -0.0F>=0.0F,a35=            -0.0F>=1.175494351e-38F,
    a36=            -0.0F>=2.7F,a37=            -0.0F>=3.402823466e+38F;
int a40=             0.0F>=-3.402823466e+38F,a41=             0.0F>=-2.7F,
    a42=             0.0F>=-1.175494351e-38F,a43=             0.0F>=-0.0F,
    a44=             0.0F>=0.0F,a45=             0.0F>=1.175494351e-38F,
    a46=             0.0F>=2.7F,a47=             0.0F>=3.402823466e+38F;
int a50= 1.175494351e-38F>=-3.402823466e+38F,a51= 1.175494351e-38F>=-2.7F,
    a52= 1.175494351e-38F>=-1.175494351e-38F,a53= 1.175494351e-38F>=-0.0F,
    a54= 1.175494351e-38F>=0.0F,a55= 1.175494351e-38F>=1.175494351e-38F,
    a56= 1.175494351e-38F>=2.7F,a57= 1.175494351e-38F>=3.402823466e+38F;
int a60=             2.7F>=-3.402823466e+38F,a61=             2.7F>=-2.7F,
    a62=             2.7F>=-1.175494351e-38F,a63=             2.7F>=-0.0F,
    a64=             2.7F>=0.0F,a65=             2.7F>=1.175494351e-38F,
    a66=             2.7F>=2.7F,a67=             2.7F>=3.402823466e+38F;
int a70= 3.402823466e+38F>=-3.402823466e+38F,a71= 3.402823466e+38F>=-2.7F,
    a72= 3.402823466e+38F>=-1.175494351e-38F,a73= 3.402823466e+38F>=-0.0F,
    a74= 3.402823466e+38F>=0.0F,a75= 3.402823466e+38F>=1.175494351e-38F,
    a76= 3.402823466e+38F>=2.7F,a77= 3.402823466e+38F>=3.402823466e+38F;
int b00=    2.71828F>=2.71828F,b01=    2.71828F>=2.71828182F,b02=    2.71828F>=2.718281828F;
int b10= 2.71828182F>=2.71828F,b11= 2.71828182F>=2.71828182F,b12= 2.71828182F>=2.718281828F;
int b20=2.718281828F>=2.71828F,b21=2.718281828F>=2.71828182F,b22=2.718281828F>=2.718281828F;

void f0(float x) {
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
}

void f1(float x) {
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
}

void g0(float x) {
  printf(s3,x>=2.71828F,x>=2.71828182F,x>=2.718281828F);
}

void g1(float x) {
  printf(s3,2.71828F>=x,2.71828182F>=x,2.718281828F>=x);
}

int op(float x,float y) { return x>=y; }

void f2(float x) {
  printf(s8,op(x,-3.402823466e+38F),op(x,-2.7F),op(x,-1.175494351e-38F),op(x,-0.0F),
            op(x,0.0F),op(x,1.175494351e-38F),op(x,2.7F),op(x,3.402823466e+38F));
}

void g2(float x) {
  printf(s3,op(x,2.71828F),op(x,2.71828182F),op(x,2.718281828F));
}

void main1() {
  float x;
  x=-3.402823466e+38F;
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  x=-2.7F;
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  x=-1.175494351e-38F;
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  x=-0.0F;
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  x=0.0F;
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  x=1.175494351e-38F;
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  x=2.7F;
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  x=3.402823466e+38F;
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
  printf(s8,x>=-3.402823466e+38F,x>=-2.7F,x>=-1.175494351e-38F,x>=-0.0F,
            x>=0.0F,x>=1.175494351e-38F,x>=2.7F,x>=3.402823466e+38F);
}

void main2() {
  float x;
  x=2.71828F;
  printf(s3,x>=2.71828F,x>=2.71828182F,x>=2.718281828F);
  printf(s3,x>=2.71828F,x>=2.71828182F,x>=2.718281828F);
  x=2.71828182F;
  printf(s3,x>=2.71828F,x>=2.71828182F,x>=2.718281828F);
  printf(s3,x>=2.71828F,x>=2.71828182F,x>=2.718281828F);
  x=2.718281828F;
  printf(s3,x>=2.71828F,x>=2.71828182F,x>=2.718281828F);
  printf(s3,x>=2.71828F,x>=2.71828182F,x>=2.718281828F);
}

void main3() {
  float x;
  x=-3.402823466e+38F;
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  x=-2.7F;
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  x=-1.175494351e-38F;
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  x=-0.0F;
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  x=0.0F;
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  x=1.175494351e-38F;
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  x=2.7F;
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  x=3.402823466e+38F;
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
  printf(s8,-3.402823466e+38F>=x,-2.7F>=x,-1.175494351e-38F>=x,-0.0F>=x,
            0.0F>=x,1.175494351e-38F>=x,2.7F>=x,3.402823466e+38F>=x);
}

void main4() {
  float x;
  x=2.71828F;
  printf(s3,2.71828F>=x,2.71828182F>=x,2.718281828F>=x);
  printf(s3,2.71828F>=x,2.71828182F>=x,2.718281828F>=x);
  x=2.71828182F;
  printf(s3,2.71828F>=x,2.71828182F>=x,2.718281828F>=x);
  printf(s3,2.71828F>=x,2.71828182F>=x,2.718281828F>=x);
  x=2.718281828F;
  printf(s3,2.71828F>=x,2.71828182F>=x,2.718281828F>=x);
  printf(s3,2.71828F>=x,2.71828182F>=x,2.718281828F>=x);
}

int main() {
  printf(s8,a00,a01,a02,a03,a04,a05,a06,a07);
  printf(s8,a10,a11,a12,a13,a14,a15,a16,a17);
  printf(s8,a20,a21,a22,a23,a24,a25,a26,a27);
  printf(s8,a30,a31,a32,a33,a34,a35,a36,a37);
  printf(s8,a40,a41,a42,a43,a44,a45,a46,a47);
  printf(s8,a50,a51,a52,a53,a54,a55,a56,a57);
  printf(s8,a60,a61,a62,a63,a64,a65,a66,a67);
  printf(s8,a70,a71,a72,a73,a74,a75,a76,a77);
  printf(s3,b00,b01,b02);
  printf(s3,b10,b11,b12);
  printf(s3,b20,b21,b22);

  main1();
  main2();
  main3();
  main4();

  f0(-3.402823466e+38F); f0(-2.7F); f0(-1.175494351e-38F); f0(-0.0F);
  f0(0.0F); f0(1.175494351e-38F); f0(2.7F); f0(3.402823466e+38F);
  g0(2.71828F); g0(2.71828182F); g0(2.718281828F);

  f1(-3.402823466e+38F); f1(-2.7F); f1(-1.175494351e-38F); f1(-0.0F);
  f1(0.0F); f1(1.175494351e-38F); f1(2.7F); f1(3.402823466e+38F);
  g1(2.71828F); g1(2.71828182F); g1(2.718281828F);

  f2(-3.402823466e+38F); f2(-2.7F); f2(-1.175494351e-38F); f2(-0.0F);
  f2(0.0F); f2(1.175494351e-38F); f2(2.7F); f2(3.402823466e+38F);
  g2(2.71828F); g2(2.71828182F); g2(2.718281828F);

  return 0;
}
