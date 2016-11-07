{$R+,S+,I+,D+,F-,V+,B-,L+ }
{$M 65520,0,655360 }
{ numeric coprocessor option N+ obsolete}
Program BootLOGN (infile, outfile, OUTPUT);

{  This program reads RAW TRUNCATED SPECIES COUNTS, AND ESTIMATES
   THE UNDERLYING ABUNDANCE DISTRIBUTION USING COHEN'S METHOD OF
   MAXIMUM LIKELIHOOD FOR DOUBLY TRUNCATED NORMAL DATA.

   Original FORTRAN Lognormal Program author:  George Sugihara, 1977
              Version 1.0
              Comments from George Sugihara are usually ALL CAPS

   Program converted to PASCAL and Bootstrapping estimator added
   by George D.F. Wilson, June 1987, Version 2.0

   Modified Aug 1987 to correct for S* estimates less than
   observed number of species.  BOOTLOGN Version 2.1.   GW

   Modifed Nov 1987: Simulated sampling of known distributions
     has shown that use of Spp_in_Sample to calculate S* gives a better
     results.  This version has been modified with this correction.
     One loop has been optimized for faster execution.
     Several of the variable names have been changed to be more
     self-explanatory.  BOOTLOGN Version 2.2.  GW.

   Modified Mar 1988: Added 95% confidence limits calculator
                      BOOTLOGN version 2.3.  GW.

   Modified Jul-Aug 1988:
                      Added Chi Square goodness of fit probability
                      Corrected the Chi Square comparisons of
                        observed and expected
                      Corrected problem with confidence limit output
                      Changed bootstrap output to table form
                      Broke some large procedures into separate procedures
                      Still need to de-globalize many variables
                       and other cleaning needed
                      BOOTLOGN version 2.4.  GW.

   Modified 30 April 1992:
                      Used CHIPROB to filter out bad data sets during
                      bootstrapping, with a probability less than 0.005
                      (usually 0.0000).  This curbs the tendancy for the
                      S* estimates to be skewed to values higher than
                      the original estimate.
                      BOOTLOGN version 2.5, GW.
   Modified 28 October 2016 
                        Compiled using FreePascal under LINUX, using the
                        Turbo Pascal Compatibility mode. 
                       consol command in code directory
                       fpc -Fu/usr/lib/fpc/3.0.0/fpmkinst/x86_64-linux/rtl \
                       -Mtp -TLINUX testbln2016.pas                        
																GW

   Known bugs, Oct 2016: Generating a Theory.dat from a previous Theory.dat
   has the same number of species but with increasing numbers of individuals.
   The curve, however, appears to be identical.

   DATA FILE FORMAT consists of data from a single pooled sample.
   The FIRST line contains the banner line, a sample identifier
   that can be up to 80 characters long.
   The SECOND line is the bootstrap line containing OPTIONS separated
   by spaces.
    - The first item is the desired number of iterations of the bootstrap
      estimator.  ----> If no bootstrapping desired, enter 0.
    - The optional second item is LIST which causes the output
      of the raw bootstrapped samples.
    - The optional third item is STATS which causes the output
      of statistics on each bootstrapped sample.
    - Defaults are No LIST and No STATS.
    - An optional fourth item is TLIST which will cause the generation of
      a file named 'THEORY.DAT' in the default directory.  This file contains
      simulated data based on the estimated theoretical distribution.  This
      data can then be used in other programs such as rarefaction curve
      generators.
    - The optional fifth item is ACCEPT which will cause the acceptance of
      analyses where S* is less than the observed number of species.  If this
      is not acceptable (DEFAULT), then S* will be recalculated without
      splitting half of the ones below the veil line, and bootstrapping will
      continue on this basis.
      (Note: as of version 2.3, this should no longer be a problem, but
             I left the code in anyway)

   The remaining lines contain the abundances of each species, one
   abundance per line.

   Input & output redirection is enabled:
   OUTPUT is to the MS-DOS standard Device CON, but it can be redirected
   to a printer, file or whatever.  Printout can be obtained by pressing
   Ctrl-PrtSc before starting the program when output goes to the screen.
}

Uses
  Crt;  {Only needed to clear the screen at the beginning of program}

CONST
   MAXSPP = 400;   {Sets arrays for maximum expected number of species.
                    It will be necessary to increase this value
                    for very diverse samples or decrease it to save
                    space if this program is included as a module
                    in a larger memory-hungry program}
   LOG_BASE =  2.0;
   MAX_REAL = 306;  {for 8087 version
                     change to 38 for non-8087 version}
   Large_Community = 100;
         {largest expected number of abundance categories (octaves)
          needs to be fairly large to account for bootstrapping estimates,
          which can be absurdly large in weak data}
VAR

  GaussPi, S2, V1, V2, ANSP, PI_X, S : DOUBLE;
  Inds_in_Sample, CHI, CHIPROB, TOT_SPECIES,
       Spp_SampDist, STDV, MEAN, ENTROPY, EVEN, I1, I2 : DOUBLE;
  MIN_Sstar, MAX_Sstar, SUM_Sstar, SUM_Sstar2 : DOUBLE; {for bootstrap estimates}
  FREQ1, PSEUDO : Array [1..MAXSPP] of REAL;
  OCT, FREQ2, FREQ3 : Array [1..Large_Community] of Real;
  Num_Rejects, MODE,
       Spp_in_Sample, I, L, M,  Max_Octave, EE12, Num_Iters :  INTEGER;
  INT_ARRAY : Array [0..Large_Community] of Integer;
  A : Array [1..7,1..7] of Integer;
  outfile, INFILE : TEXT;
  Station_Name, filename : String[80];
  DATA_OK, BOOTING, GO_BOOT, LIST, STATS, TLIST,
                      RETRY, FIRST_OK, Try_Again : BOOLEAN;

Function LARGEST (Num1, Num2: INTEGER): INTEGER;
Begin
  IF Num1 >= Num2 THEN
     LARGEST := Num1
  ELSE
     LARGEST := Num2;
End;

Function TRUNK (RN : REAL): INTEGER;
{This function is necessary to correct for inaccurate internal
 representation of real numbers in non-8087 Turbo Pascal.
 It appears to have no effect in the 8087 version.}

BEGIN
  TRUNK := TRUNC(RN + 0.0000000001);
END;

FUNCTION gammln(xx: DOUBLE): DOUBLE;
{This function from Press et al 1986}
      CONST
        stp = 2.50662827465;
        half = 0.5;
        one = 1.0;
        fpf = 5.5;
      VAR
        x,tmp,ser: double;
        j: integer;
        cof: ARRAY [1..6] OF double;
      BEGIN
        cof[1] := 76.18009173;
        cof[2] := -86.50532033;
        cof[3] := 24.01409822;
        cof[4] := -1.231739516;
        cof[5] := 0.120858003e-2;
        cof[6] := -0.536382e-5;
        x := xx-one;
        tmp := x+fpf;
        tmp := (x+half)*ln(tmp)-tmp;
        ser := one;
        FOR j := 1 to 6 DO BEGIN
           x := x+one;
           ser := ser+cof[j]/x
          END;
        gammln := tmp+ln(stp*ser)
      END;

FUNCTION SAM(COUNT:REAL; N:INTEGER): DOUBLE;

{ THIS FUNCTION CALCULATES THE N'TH SAMPLE MOMENT
    Max_Octave and INT_ARRAY[] are treated as global variables
    and INT_ARRAY is not reDIMENSIONed as in the original program
}
VAR
  PRESAM, XI : DOUBLE;
  I : INTEGER;
BEGIN
   PRESAM := 0.0;
   FOR I := 1 TO Max_Octave DO
     BEGIN
       XI := I-0.5;
       CASE N OF
        1 : BEGIN
             PRESAM := PRESAM + (INT_ARRAY[I]/2.0)*(XI);
            END;
        2 : BEGIN
             PRESAM := PRESAM + (INT_ARRAY[I]/2.0)*SQR(XI);
            END
        ELSE PRESAM := PRESAM + (INT_ARRAY[I]/2.0)*EXP(N*LN(XI));
        {added as an afterthot - to allow generality}
       END; {case}
     END;  {for}
   SAM := PRESAM/COUNT;
END; {function SAM}

FUNCTION GAUSS1(X:real): DOUBLE;
        {  PROBABILITY DENSITY FOR UNIT NORMAL  }
BEGIN
 GAUSS1 :=  GaussPi * EXP(-0.5 * SQR(X));
END;

FUNCTION GAUSS2(XBAR,STDV,XI:REAL): DOUBLE;
{  PROBABILITY DENSITY FOR GENERAL NORMAL  }
var
  X : DOUBLE;
BEGIN
  X := (XBAR-XI)/STDV;
  GAUSS2 := GaussPi * (1.0/STDV) * EXP(-0.5 * SQR(X));
END;  {function GAUSS2}

FUNCTION TRAP(E,B:REAL; N:INTEGER):REAL;
{  THIS FUNCTION INTEGRATES THE GAUSSIAN DISTRIBUTION USING
   THE TRAPEZOIDAL RULE
   GAUSS1, the REAL function is global and not part of the
   function parameters as in the original program (as GAUSS)
}
Var
  H, SUM, X : DOUBLE;
  I, K : INTEGER;
BEGIN
  {E = the starting point,
   B = the stopping point of the integration}
  H := (B-E)/N;
  {H is the unit of integration along abscissa}
  SUM := 0.0;
  K := N-1;
  {K = number of integration units}
  FOR I := 1 TO K DO
    BEGIN
      X := E + (I * H);
      {X is distance from starting point to current postion }
      SUM := SUM + GAUSS1(X);
      {calculates length of the ordinate at the current position
       and sums over all positions}
    END;
  TRAP := (GAUSS1(E) + GAUSS1(B) + (2.0 * SUM)) * (H/2.0) + 0.0001;
  {i.e. twice the length of all the ordinates, include length of
  two end points, multiply by half the unit width, and
  add a small correction}
END;  {function trap}

Procedure LOGO;
   BEGIN
      ClrScr;
      WRITELN(outfile, '                BOOTLOGN Version 2.5');
      WRITELN(outfile, 'Community Structure: LogNormal Distribution Estimation');
      WRITELN(OUTPUT,
'                           BOOTLOGN Version 2.5');
      WRITELN(OUTPUT,
'            Community Structure: Log Normal Distribution Estimation');
      WRITELN(OUTPUT,
'          with bootstrap estimation of theoretical number of species');
      WRITELN(OUTPUT,
'                       by George D.F. Wilson, 1987, 1988, 1992, 2016');
      WRITELN(OUTPUT,
'                               Saugatuck Natural History Laboratory');
      WRITELN(OUTPUT,
'    Original doubly truncate lognormal fitting program by George Sugihara');
      WRITELN(OUTPUT);
   END;{Procedure LOGO}

Procedure INIT_VAR;
Var
  I, J  : INTEGER;
 BEGIN
    Randomize;  {This should be called only once during the program}
    FOR I :=1 TO 7 DO
        FOR J :=1 TO 7 DO
            A[I,J] := 0;  { Apparently not all array members are
                            used, but it seems a good idea to zero
                            the array anyway}
    A[1,1] := 243;
    A[2,1] := -837;
    A[2,2] := 1236;
    A[3,2] := 429;
    A[4,2] := -326;
    A[1,3] := 2842;
    A[2,3] := 2233;
    A[3,3] := 1727;
    A[4,3] := 1323;
    A[5,3] := 319;
    A[6,3] := 17;
    A[1,4] := 3535;
    A[2,4] := 2828;
    A[3,4] := 2323;
    A[4,4] := 1919;
    A[5,4] := 1616;
    A[6,4] := 1111;
    A[7,4] := 606;
    A[1,5] := 4228;
    A[2,5] := 3322;
    A[3,5] := 2816;
    A[4,5] := 2312;
    A[5,5] := 1907;
    A[6,5] := 1700;
    A[2,6] := 3611;
    A[3,6] := 2906;
    A[4,6] := 2608;
    A[1,7] := 4303;
    A[2,7] := 3510;
    A[5,2] := -326;
    GaussPi := 1/sqrt(2 * Pi);
    DATA_OK := TRUE;
    BOOTING := FALSE;
    GO_BOOT := FALSE;
    RETRY := FALSE;
    FIRST_OK := TRUE;
    Try_Again := TRUE;
    LIST := FALSE;
    STATS := FALSE;
    TLIST := FALSE;
    SUM_Sstar := 0.0;
    SUM_Sstar2 := 0.0;
    Num_Rejects := 0;
    For I := 1 to MaxSpp DO FREQ1[I] := 0.0;
    For I := 1 to Large_Community DO FREQ3[I] := 0.0;
    For I := 1 to Large_Community DO FREQ2[I] := 0.0;
    For I := 1 to Large_Community DO OCT[I] := 0.0;
END;  {procedure INIT_VAR}

PROCEDURE Get_Data;
{ Load data from user-designated file, and accumulate variables }
 VAR
   Inds_in_this_Sp : DOUBLE;

  Procedure GetOptions;
   var
     ch : char;
     instring : string[10];
     counter : integer;
   begin
     While not EOLN(infile) do
     begin
       instring := '        ';
       READ(infile, ch);
       IF ch <> ' ' then
         begin
           counter := 1;
           instring[counter] := upcase(ch);
           while not ((ch = ' ') or eoln(infile)) do
             begin
              read(infile, ch);
              counter := counter + 1;
              instring[counter] := upcase(ch);
            end; {while}
           case instring[1] of
           'A' : Try_Again := FALSE;
           'L' : begin
                  LIST := TRUE;
                  Writeln(outfile,
                  'Pseuodata used in bootstrapping will be listed');
                 end;
           'S' : begin
                   STATS := TRUE;
                   Writeln(outfile,
                   'Statistics from each bootstrap sample will be given');
                 end;
           'T' : begin
                   TLIST := TRUE;
                   Writeln(outfile,
 'A new dataset resembling the theoretical distribution will be generated');
                   Writeln(outfile, '   in the file named THEORY.DAT');
                 end
           else begin
              Write(outfile, 'Bad Output Option = ');
              For I := 1 to 8 do Write(outfile,instring[i]);
              Writeln(outfile);
              writeln(outfile,'Program Terminated');
              CLOSE(outfile);
              HALT;
             end; {case}
         end; {if}
        end; {case}
      end; {while}
    end; {GetOption}

BEGIN
  READLN(INFILE, Station_Name);
  {Output will be quoted to allow labels to be inputted into other programs}
  WRITELN(outfile,'"',Station_Name,'"');
  READ(INFILE, Num_Iters);
  IF Num_Iters > 0 THEN
    BEGIN
      GO_BOOT := TRUE;
      WRITELN(outfile,'Bootstrap estimation will be used');
      WRITELN(outfile,'Mean S* will be calculated from the original S* and ',
                      Num_Iters,' bootstrap estimates.');
    END;
  GetOptions;
  Spp_in_Sample := 0;
  Inds_in_Sample := 0.0;
  WHILE NOT EOF(INFILE) DO
     BEGIN
        READLN(INFILE,Inds_in_this_Sp);
        {  FIND THE NUMBER OF SPECIES AND INDIVIDUALS IN THE SAMPLE
           FREQ OF JTH SPECIES IN SAMPLE = FREQ1(J)
           THE NUMBER OF SPECIES IN THE SAMPLE = Spp_in_Sample
           THE NUMBER OF INDIVIDUALS IN THE SAMPLE = Inds_in_Sample   }
        Spp_in_Sample := Spp_in_Sample + 1;
        Inds_in_Sample := Inds_in_Sample + Inds_in_this_Sp;
        FREQ1[Spp_in_Sample] := Inds_in_this_Sp;
     END;   {while not eof(infile)}
END; {Procedure Get_Data}

Procedure Data_Intervals;
 {  DIVIDE DATA INTO LOG BASE  INTERVALS, SPLITTING THOSE VALUES
    THAT FALL ON INTERVAL DIVISION POINTS BETWEEN THE TWO ADJACENT OCTAVES
    2X SPECIES IN SAMPLE DIST = INT_ARRAY(J)    }
Var
  I, J : INTEGER;
  Inds_in_this_Sp : DOUBLE;

BEGIN
    FOR I := 1 TO Large_Community DO OCT[I] := 0.0;
    Spp_SampDist := 0.0;
    Max_Octave := 1;
    FOR J := 0 TO Large_Community DO
        INT_ARRAY[J] := 0;
    FOR I := 1 TO Spp_in_Sample DO
      BEGIN
        IF BOOTING THEN Inds_in_this_Sp := PSEUDO[I]
                   ELSE Inds_in_this_Sp := FREQ1[I];
        S := LN(Inds_in_this_Sp)/LN(LOG_BASE);
        J := TRUNK(S) + 1;
        {replaced Sugihara's FORTRAN routine with new one that depends on the
         accuracy of the LN calculation - which is good enough for
         the current application.  Note that INT_ARRAY has been altered
         to have a 0 index that is not accessed.  This solves the problem
         of what to do with the half of the 1 values that are chucked
         behind the veil line.  Problems in the original were probably
         caused by the truncation routine which have been fixed by the
         adjusted function TRUNK.  }
        IF (J > Max_Octave) THEN Max_Octave := J;
        IF TRUNK(J-S) = 1 THEN
          BEGIN
            IF Inds_in_this_Sp = 1 THEN
              begin
               IF RETRY THEN
                 begin
                    Spp_SampDist := Spp_SampDist + 1.0;
                    INT_ARRAY[J] := INT_ARRAY[J] + 2;
                 end
               ELSE
                 begin
                   Spp_SampDist := Spp_SampDist + 0.5;
                   INT_ARRAY[J] := INT_ARRAY[J] + 1;
                   INT_ARRAY[J-1] := INT_ARRAY[J-1] + 1;
                 end
              end
            ELSE
              begin
               Spp_SampDist := Spp_SampDist + 1.0;
               INT_ARRAY[J] := INT_ARRAY[J] + 1;
               INT_ARRAY[J-1] := INT_ARRAY[J-1] + 1;
              end
          END
        ELSE
          BEGIN
            Spp_SampDist := Spp_SampDist + 1.0;
            INT_ARRAY[J] := INT_ARRAY[J] + 2;
          END;
    END; {for - loading Int_Array}
   FOR I :=1 TO Max_Octave DO OCT[I] := INT_ARRAY[I]/2;
END; { Data_Intervals }

Procedure MAKE_PSEUDO;
{  Creates pseudo-data sets from original frequencies of each species
   The new data sets contain the same number of species and individuals
   but have randomly differing distributions among the species.
   Individuals are added to the species based on their frequency, but
   with replacement, so that the new frequencies will randomly vary.  }
   Const
     Segments = 10;
     { This value is optimized for taxocenes of 100 spp
       If smaller species richnesses are used, reduce Segments
       If larger species richnesses occur, increase Segments
       Future versions may optimize Segments automatically
     }

   Var
    I, Sp_Index : INTEGER;
    Ind_Index, Inds_Left, Zeros : DOUBLE;
    Cum_Freq1 : array[1..MaxSpp] of Real;
    Seg_Index : array[0..Segments] of integer;

  Begin
    FOR  I := 1 to random(201)+1 DO Zeros := random(I);
    {advances the random number generator a random number of iterations}
    Inds_Left := Inds_in_Sample;
    Zeros := Spp_in_Sample;
    FOR I := 1 to MAXSPP DO PSEUDO[I] := 0.0;
    Cum_Freq1[1] := FREQ1[1];
    FOR I := 2 to Spp_in_Sample DO Cum_Freq1[I] := Cum_Freq1[I-1] + FREQ1[I];
    FOR I := 1 TO (Segments - 1) DO Seg_Index[I] := I * trunc(Spp_in_Sample/segments);
    Seg_Index[0] := 1;
    Seg_Index[Segments] := Spp_in_Sample;
    WHILE Inds_Left > Zeros DO
     begin
      Ind_Index := int((1 - RANDOM)*Inds_in_Sample);
      I := 0;
      Repeat
        I := I + 1;
      Until (Cum_Freq1[Seg_Index[I]] >= Ind_Index);
       { Finds segment that contains the species with Ind_Index }
      Sp_Index := Seg_Index[I - 1];
      WHILE Cum_Freq1[Sp_Index] < Ind_Index DO Sp_Index := Sp_Index + 1;
        {finds species index equivalent to the random individual number}
      IF PSEUDO[Sp_Index] = 0 THEN Zeros := Zeros - 1;
      PSEUDO[Sp_Index] := PSEUDO[Sp_Index] + 1;
      Inds_Left := Inds_Left - 1;
     end; {While Zeros}
    FOR I := 1 TO Spp_in_Sample DO IF PSEUDO[I] = 0 THEN PSEUDO[I] := 1;
    IF LIST THEN
     begin
       WRITELN(outfile, 'Raw Bootstrapped Sample no. ',M,':');
       For L := 1 to Spp_in_Sample do write(outfile,pseudo[L]:8:0);
       WRITELN(outfile);
     end;
  END; {Make Pseudo distribution}

PROCEDURE Describe;

{ This procedure will decribe the original data and print the results.
  The original lineprinter graphic HISTO is removed. }

Var
  I, J, K, L  :  INTEGER;
BEGIN
      MODE := INT_ARRAY[1];  {  FIND THE MODAL FREQUENCY }
      FOR I := 2 TO Max_Octave DO
            IF  (INT_ARRAY[I] > MODE) THEN MODE := INT_ARRAY[I];
      ENTROPY := 0;       {  FIND DIVERSITY AND EVENNESS  }
      FOR K := 1 TO Spp_in_Sample DO
        BEGIN
          PI_X := FREQ1[K]/Inds_in_Sample;
          ENTROPY := ENTROPY-(PI_X*LN(PI_X));
        END;
      ANSP := Spp_in_Sample;
      EVEN := ENTROPY/LN(ANSP);
      {DETERMINE THE FIRST TWO SAMPLE MOMENTS ABOUT THE LOWER TRUNCATION
       POINT, WHERE V1 IS THE FIRST SAMPLE MOMENT AND V2 IS THE SECOND
       SAMPLE MOMENT  }
      V1 := SAM(Spp_SampDist, 1);
      V2 := SAM(Spp_SampDist, 2);
      S2 := V2-SQR(V1);      {  DETERMINE SAMPLE VARIANCE  }
      IF NOT BOOTING THEN
        Begin
          WRITELN(outfile);
          WRITELN(outfile,'"Original Truncated Data:"');
          IF RETRY THEN
            WRITELN(outfile,
              '"Recalculated without splitting half of the ones ',
              'below the veil line."');
          WRITELN(outfile,'   "Octave"  "No. Spp."');
          FOR I := 1 TO Max_Octave DO
              WRITELN(outfile, i:10, (INT_ARRAY[i]/2):10:1);
          WRITELN(outfile);
          WRITELN(outfile,'"RAW SAMPLE STATISTICS:"');
          WRITELN(outfile,'           "First Sample Moment" =    ',V1:8:4);
          WRITELN(outfile,'          "Second Sample Moment" =    ',V2:8:4);
          WRITELN(outfile,'               "Sample Variance" =    ',S2:8:4);
          WRITELN(outfile,
          '"Species in Sample Distribution" = ',Spp_SampDist:8:1);
          WRITELN(outfile,
          '             "Species in Sample" = ',  Spp_in_Sample:6);
          WRITELN(outfile,'         "Individuals in Sample" = ',  Inds_in_Sample:6:0);
          WRITELN(outfile,'          "Mode of Distribution" =    ',(MODE/2):6:2);
          WRITELN(outfile,'                "Sample Entropy" =    ',ENTROPY:8:4);
          WRITELN(outfile,'               "Sample Evenness" =    ',EVEN:8:4);
          WRITELN(outfile);
        end; {If not booting}
END; {procedure Describe}


PROCEDURE Analyze;

VAR
   I, J, K, L, N, NDIV1, NDIV2 : INTEGER;
   IGAUSS, IWIDE1, IWIDE2 : INTEGER;
   Max_Oct_Real, P1, P2, E1, E2, S, T, BPOINT, TPOINT : DOUBLE;
   XI, AREA, TRUNC_SAMP, Interval_Term : DOUBLE;
   ANSP, AINDV, HSTAR, ESTAR  : DOUBLE;

  Function Unstable: BOOLEAN;     {  DEFINE UNSTABLE BOUNDARIES  }
   var I : Integer;
    begin
      Unstable := FALSE;
      IF ((J < 1) OR (K < 1) OR (K > 7)) THEN Unstable := TRUE;
      FOR  I := 2 TO 4 DO
        BEGIN
          N := I+3;
          IF ((K = I) AND (J > N )) THEN Unstable := TRUE;
        END;
      N := 8;
      FOR I := 5 TO 7 DO
        BEGIN
         N := N-2;
         IF ((K = I) AND (J > N)) THEN Unstable := TRUE;
        END;
      IF (K = 1) AND (J > 2) THEN Unstable := TRUE;
      IF (K = 2) AND (J < 2) THEN Unstable := TRUE;
      IF (K = 6) AND (J < 2) THEN Unstable := TRUE;
   End;  {function Unstable}

   Procedure Ml_Cohen;
   { MAXIMUM LIKELIHOOD SOLUTIONS OF COHEN'S EQUATIONS:
     THIS IS A MODIFICATION OF NEWTON'S METHOD FOR THE SOLUTION OF
     SIMULTANEOUS NON-LINEAR DIFFERENTIAL EQUATIONS,
     WHICH CONVERGES FASTER. }
   Var
     Done : BOOLEAN;
     B, D, Z1, Z2, ALPHA, ZETA : DOUBLE;

   Procedure Init;
     begin
      EE12 := A[J,K];
      E2 := ABS((EE12 MOD 100)/10.0);
                  { TWO EXCEPTIONAL CASES FOR E2  }
      IF ((J = 4) AND (K = 6) OR (J = 2) AND (K = 7)) THEN E2 := -E2;
      E1 := -TRUNK(EE12/100.0)/10.0;
      {  Well, we don't really need to know the values of E1 and E2
         The output of these values is commented out to save
         space on the printout.
         If you really want it, we can remove the curly brackets.
      IF NOT BOOTING THEN
        BEGIN
           WRITELN(outfile,'"First Estimate of E1" = ',E1:9:5);
           WRITELN(outfile,'"First Estimate of E2" = ',E2:9:5);
        END;
      }
      end; {procedure init within ML_Cohen}

   BEGIN {ML_Cohen}
      Init;
      Done := FALSE;
      P1 := E1;
      P2 := E2;
      REPEAT
        NDIV1 := 45;
        NDIV2 := 25;
        IF (E1 < 0.0) THEN NDIV1 := 60;
        IF (E2 < 2.0) THEN NDIV2 := 35;
        B := 3.80;
        I1 := TRAP(E1,B,NDIV1);
        I2 := TRAP(E2,B,NDIV2);
        D := I1-I2;
        Z1 := GAUSS1(E1)/D;
        Z2 := GAUSS1(E2)/D;
        ALPHA := Z1 - Z2;
        ZETA := ALPHA * S + Z2;
        E2 := ALPHA+(ZETA-SQRT(SQR(ZETA)+4.0*T))*Max_Oct_Real*(V1-Max_Oct_Real)/(2.0*S2);
        E1 := -(E2 * S - ALPHA) / (1.0 - S);
        IF (ABS(E1-P1) <= 0.001) THEN Done := TRUE;  {exit from procedure}
        IF NOT Done THEN
          BEGIN
            IF (ABS(E1-P1) > 0.002) THEN E1 := (2.0 * E1) - P1;
            IF (ABS(E2-P2) > 0.002) THEN E2 := (2.0 * E2) - P2;
            P1 := E1;
            P2 := E2;
          END;
      UNTIL DONE;
    End; {Procedure Ml_Cohen}

  PROCEDURE WRITE_THEORETICAL;
  VAR
    TFILE : TEXT;
    INDS_PER_SP, I, INTERVALS, J : INTEGER;
    FRACTION : DOUBLE;

   BEGIN
     ASSIGN(TFILE, 'THEORY.DAT');
     REWRITE(TFILE);
     WRITELN(TFILE, 'Theoretical Abundances of ', Station_Name);
     for I := 1 to IWIDE2 do
      BEGIN
       FRACTION := 0.0;
       INTERVALS := ROUND(FREQ3[I]);
       FOR J := 1 TO INTERVALS DO
        BEGIN
         FRACTION := FRACTION + 1/(INTERVALS+1);
         INDS_PER_SP := ROUND(EXP((I-(1-FRACTION))*LN(LOG_BASE)));
         WRITELN(TFILE, INDS_PER_SP);
        END;
      END;
      CLOSE(TFILE);
   END; {WRITE_THEORETICAL}

   PROCEDURE Get_Chi_Square;
      {  EVALUATE CHI-SQUARE AND CALCULATE PROBABILITY DIFFERS DUE TO CHANCE}

    CONST
      itmax_size = 30000;

    VAR
     DF, K: Integer;
     Observed, Expected : Double;

     PROCEDURE gser(a,x: DOUBLE; VAR gamser,gln: DOUBLE);
        LABEL 1;
        CONST
          itmax=itmax_size;
          eps=3.0e-7;
        VAR
        n: integer;
        sum,del,ap: DOUBLE;
      BEGIN
        gln := gammln(a);
        IF (x <= 0.0) THEN BEGIN
           IF (x < 0.0) THEN BEGIN
             writeln(outfile,'Error in Statistics calculation')
             {'pause in GSER - x less than 0'); readln}
            END;
           gamser := 0.0
          END ELSE BEGIN
              ap := a;
              sum := 1.0/a;
              del := sum;
              FOR n := 1 to itmax DO BEGIN
                ap := ap+1.0;
                del := del*x/ap;
                sum := sum+del;
                IF (abs(del) < abs(sum)*eps) THEN GOTO 1
               END;
              writeln(outfile,'Error in Statistics calculation');
              {('pause in GSER - a too large, itmax too small'); readln;}
              1:      gamser := sum*exp(-x+a*ln(x)-gln)
         END
      END;

    PROCEDURE gcf(a,x: DOUBLE; VAR gammcf,gln: DOUBLE);
      LABEL 1;
      CONST
        itmax=itmax_size;
        eps=3.0e-7;
      VAR
        n: integer;
        gold,g,fac,b1,b0,anf,ana,an,a1,a0: DOUBLE;
      BEGIN
        gln := gammln(a);
        gold := 0.0;
        a0 := 1.0;
        a1 := x;
        b0 := 0.0;
        b1 := 1.0;
        fac := 1.0;
        FOR n := 1 to itmax DO BEGIN
            an := 1.0*n;
            ana := an-a;
            a0 := (a1+a0*ana)*fac;
            b0 := (b1+b0*ana)*fac;
            anf := an*fac;
            a1 := x*a0+anf*a1;
            b1 := x*b0+anf*b1;
            IF (a1 <> 0.0) THEN BEGIN
               fac := 1.0/a1;
               g := b1*fac;
               IF (abs((g-gold)/g) < eps) THEN GOTO 1;
               gold := g
             END
         END;
         writeln(outfile,'Error in Statistics calculation');
         {('pause in GCF - a too large, itmax too small'); readln;}
         1:   gammcf := exp(-x+a*ln(x)-gln)*g
      END;

   FUNCTION gammq(a,x: DOUBLE): DOUBLE;
      VAR
        gamser,gln: DOUBLE;
     BEGIN
        IF ((x < 0.0) OR (a <= 0.0)) THEN BEGIN
           writeln(outfile,'Error in Statistics calculation')
           {('pause in GAMMQ - invalid arguments'); readln}
          END;
        IF (x < a+1.0) THEN BEGIN
             gser(a,x,gamser,gln);
             gammq := 1.0-gamser
          END ELSE BEGIN
             gcf(a,x,gamser,gln);
             gammq := gamser
          END
     END;

    BEGIN  {PROCEDURE Get_Chi_Square}
      CHI := 0.0;
      DF := -3;
      {We have to use DF=K-3 because both the mean and standard deviation
       were estimated from the data to calculate the expected frequency   }
      FOR K := 1 TO Max_Octave DO
       begin
         IF (FREQ2[K] <> 0.0) THEN    {prevents division by zero}
          BEGIN
            IF (abs(ln(abs(OCT[K]-FREQ2[K]))/ln(10) -
              ln(abs(FREQ2[K]))/ln(10)) > MAX_REAL) THEN
              begin            {avoids flop overflow}
                 DATA_OK := FALSE;
                 WRITELN(outfile,
                 'Chi Square ERROR: Value to be calculated was',
                 ' too small or too large!');
                 IF NOT BOOTING THEN FIRST_OK := FALSE
              end ELSE          {accumulate Chi square value}
                 Expected := FREQ2[K];
                 Observed := OCT[K]*(Spp_in_Sample/Spp_SampDist);
          { In order to Freq2 and Oct equivalent, a correction must be
            used:  Increase the observed using the sample/distribution
            species ratio.  This makes the totals equivalent and
            mimics the process used to calculate S*.
            This also improves the chi square value by quite a bit
            because the observed and expected are more comparable.  }
                 CHI := CHI+(SQR(Observed-Expected)/Expected);
                 DF := DF + 1;
              END
          ELSE  {Print warning that expected was zero}
              WRITELN(outfile, 'Chi Square Problem: Expected was Zero!');
          END;  {check for zero expected}
      IF DF > 0 THEN
         CHIPROB := GAMMQ(0.5*DF,0.5*Chi)
       ELSE  Begin
         WRITELN(outfile, 'ERROR: Data set may be too small!');
         CHIPROB := 0.0;
       END;
    END;  {PROCEDURE Get_Chi_Square}

Procedure OUTPUT_ESTIMATE_LIST;
    VAR
      I : INTEGER;
    BEGIN
          WRITELN(OUTPUT);
          WRITELN(outfile,'"THEORETICAL SPECIES UNIVERSE: "');
          WRITELN(outfile,'   "Octave"  "No. Spp."');
          FOR I := 1 TO IWIDE2 DO
              WRITELN(outfile, i:10, (INT_ARRAY[I]/2):10:1);
          WRITELN(outfile);
          WRITELN(outfile,'"ESTIMATED PARAMETERS:"');
          WRITELN(outfile,'        "Distribution Mean" = ',MEAN:8:4);
          WRITELN(outfile,'   "Distribution Std. Dev." = ',STDV:8:4);
          WRITELN(outfile,'   "Upper Truncation Point" = ',Max_Octave:3);
          WRITELN(outfile,'     "Degree of Truncation" = ',TRUNC_SAMP:8:4);
          WRITELN(outfile,'"Theoretical Species Count" =',TOT_SPECIES:9:4);
          WRITELN(outfile,'     "Mode of Distribution" = ',MODE/2:6:2);
          WRITELN(outfile,'               "Chi-Square" = ',CHI:8:4);
          WRITELN(outfile,'     "Chi-Square Fit Prob." = ',CHIPROB:8:4);
          WRITELN(outfile,'                  "Entropy" = ',ENTROPY:8:4);
          WRITELN(outfile,'                 "Evenness" = ',EVEN:8:4);
          WRITELN(outfile,'                   "H-Star" = ',HSTAR:8:4);
          WRITELN(outfile,'                   "J-Star" = ',ESTAR:8:4);
    END;{Procedure OUTPUT_ESTIMATE_LIST}

Procedure Initialize_Analysis;
   begin
      Max_Oct_Real := Max_Octave;
      {  OBTAIN TWO QUANTITIES: V1/Max_Oct_Real AND S2/SQR(Max_Oct_Real)}
      S := V1/Max_Oct_Real;
      T := S2/SQR(Max_Oct_Real);
      { *********** OBTAIN FIRST ESTIMATES OF E1 AND E2
                    WHICH ARE WITHIN A CONVERGENT NEIGHBORHOOD. *********** }
      J := TRUNK(T*100.0)-1;
      K := TRUNK(S*10.0)-1;
      IF (((T * 100.0) - J) >= 1.5) THEN J := J+1;
      IF (((S * 10.0) - K) >= 1.5) THEN K := K+1;
   end; {Initialize_Analysis}

 Procedure Calc_Params;
  begin
        { *********** CALCULATE THE MEAN AND STANDARD DEVIATION
                    FOR THE TRUNCATED SAMPLE *********** }
      STDV := Max_Oct_Real/(E2-E1);
      MEAN := -STDV*E1;
      {   Output of E1 and E2 commented out.
          If you really want these, you can remove these comments
      IF NOT BOOTING THEN
        BEGIN
           WRITELN(outfile,'"Final Estimate of E1" = ',E1:9:5);
           WRITELN(outfile,'"Final Estimate of E2" = ',E2:9:5);
        END;
      }
     { *********** ESTIMATE THE DEGREE OF TRUNCATION *********** }
      BPOINT := -MEAN/STDV;
      {BPOINT = E1 }
      TPOINT := Max_Oct_Real/STDV;
      {TPOINT = E2 - E1 }
      AREA := TRAP(BPOINT,TPOINT,50);
      TRUNC_SAMP := 1.0 - AREA; {i.e. the unit area
                                      below the lower truncation point }
      { *********** ESTIMATE TOTAL NUMBER OF SPECIES IN SAMPLING UNIVERSE  }
      TOT_SPECIES := Spp_in_Sample/AREA; {instead of Spp_SampDist!}
       {
       Original version used Spp_SampDist which often resulted in the
       estimated total species being LESS than the actual number of
       species in the sample.  This happened both where the
       distribution was poorly sampled, and where it was nearly
       completely sampled.  This paradoxical behavior is corrected
       by using the number of species in the sample, Spp_in_Sample,
       to calculate TOT_SPECIES
       }
  end; {Procedure Calc_Params in procedure analyze}

Procedure Calc_Stats; {in procedure analyze}
  var
       J : Integer;
  begin
    { *********** FIND FREQUENCIES FOR: HISTOGRAM (INT_ARRAY),
                  CHI-SQUARE (FREQ2, ENTROPY), (FREQ3) *********** }
      K := 0;
      IWIDE1 := TRUNK(Max_Oct_Real - MEAN + 1.0);
      IWIDE2 := TRUNK((Max_Oct_Real - MEAN + 1.0) * 2.0{ - 1});
              {truncation added - not in original program!}
              {the usage of IWIDE1&2 indicates that they are integers}
      Interval_Term := TRUNK(2.0 * MEAN - Max_Oct_Real) - 1.5;
      FOR  J := 1 TO IWIDE2 DO
        BEGIN
          XI := Interval_Term + J;
          FREQ3[J] := GAUSS2(MEAN,STDV,XI)*TOT_SPECIES;
          IGAUSS := TRUNK(2.0*FREQ3[J]);
          {truncation added - not in original program}
          IF (2.0*FREQ3[J]-IGAUSS >= 0.5) THEN IGAUSS := IGAUSS + 1;
          {rounds the number of species if necessary}
          INT_ARRAY[J] := IGAUSS;
          IF (XI >= 0.5) THEN
          {collect species above the lower truncation point}
           BEGIN
             K := K+1;
             FREQ2[K] := FREQ3[J];
           END; {if}
        END;  {for}
      Get_Chi_Square;
      { *********** FIND ENTROPY AND EVENNESS *********** }
      AINDV := 0;
      ANSP := 0;
      FOR J := 1 TO IWIDE2 DO
        BEGIN
{          IF FREQ3[J] = 0.0000 THEN FREQ3[J] := 0;
          another bug fix for real zeros!!}
          AINDV := AINDV+FREQ3[J]*(EXP((J-0.5)*LN(LOG_BASE)));
           {asymptotic number of individuals }
          ANSP := ANSP+FREQ3[J];
          {asymptotic number of species }
        END; {for}
      ENTROPY := 0;
      FOR J := 1 TO IWIDE2 DO
        BEGIN
          PI_X := EXP((J-0.5)*LN(LOG_BASE))/AINDV;
{          IF (PI_X <= 0.0) THEN
            BEGIN
              DATA_OK := FALSE;
              IF NOT BOOTING THEN FIRST_OK := FALSE;
              PI_X := 0.000000001;
              above line avoids passing a bad value to the LN function
            END;                                    }
          ENTROPY := ENTROPY - PI_X * LN(PI_X) * FREQ3[J];
        END;  {for}
{      IF (ANSP <= 0.0) THEN ANSP := 0.000000001;
      above line avoids passing a bad value to the LN function  }
      EVEN := ENTROPY/LN(ANSP);
      {  FIND ENTROPY USING H-STAR  }
{      IF (TOT_SPECIES <= 0.0) THEN TOT_SPECIES := 0.000000001;
      above line avoids passing a bad value to the LN function}
      HSTAR := 1.10*EXP(-0.11*STDV)*LN(TOT_SPECIES);
      ESTAR := HSTAR/LN(TOT_SPECIES);
      {  FIND MODAL FREQUENCY  }
      MODE := LARGEST(INT_ARRAY[IWIDE1],INT_ARRAY[IWIDE1+1]);
end; {Procedure Calc_Stats in procedure analyze}

BEGIN    {procedure analyze}
   Initialize_Analysis;
   DATA_OK := TRUE;
   IF Unstable THEN
        BEGIN
          DATA_OK := FALSE;
          IF NOT BOOTING THEN
            begin
              FIRST_OK := FALSE;
              WRITELN(outfile,
              'GLOBAL INSTABILITY: Cannot estimate Normal parameters!')
            end
        END;
   IF DATA_OK THEN   {skip all further analysis if not bad DATA}
     BEGIN
      Ml_Cohen;
      Calc_Params;
      IF (TOT_SPECIES < Spp_in_Sample) and NOT BOOTING THEN
       begin
         WRITELN(outfile,
         'WARNING: BAD ESTIMATE!  S* less than sample species number');
         RETRY := TRUE;
       end;
       IF NOT BOOTING THEN
          begin
            DATA_OK := (TOT_SPECIES > 0.0);
            IF NOT DATA_OK THEN BEGIN
                Writeln('Sorry: negative species number calculated!');
                Writeln('Data probably cannot be used with this program.');
                Writeln('Analysis HALTED!');
                CLOSE(outfile);
                HALT;
              END;
            FIRST_OK := DATA_OK
          end
        ELSE   DATA_OK := (TOT_SPECIES >= Spp_in_Sample);
    IF DATA_OK THEN Calc_Stats;
    {Intermediate IF DATA_OK to prevent ANY calculations taking place
           on garbage numbers, done after calculating S* (TOT_SPECIES)  }
    IF NOT BOOTING AND DATA_OK THEN
        BEGIN
          MAX_Sstar := TOT_SPECIES; {initialize for bootstraping}
          MIN_Sstar := TOT_SPECIES;
          OUTPUT_ESTIMATE_LIST;
          IF TLIST THEN WRITE_THEORETICAL;
       END; {if not booting}
  END; {if DATA_OK, done after checking for instabilities }
END;  {analyze}

Procedure Collect_Estimate;
{This can be expanded to collect estimates of the other paramters}
BEGIN
  SUM_Sstar := SUM_Sstar + TOT_SPECIES;
  SUM_Sstar2 := SUM_Sstar2 + SQR(TOT_SPECIES);
  IF MAX_Sstar < TOT_SPECIES THEN MAX_Sstar := TOT_SPECIES;
  IF MIN_Sstar > TOT_SPECIES THEN MIN_Sstar := TOT_SPECIES;
END;

Procedure Report_Estimate(N : INTEGER);
  var
    t, Interval, Variance, Standard_Deviation : DOUBLE;

FUNCTION T_Dist(DF : INTEGER):DOUBLE;
CONST
  Precision = 10000000.0;
VAR
  PROB, TPROB, T, Ttemp, TLAST :DOUBLE;

FUNCTION betacf(a,b,x: DOUBLE): DOUBLE;
LABEL 1;
CONST
   itmax=100;
   eps=3.0e-7;
VAR
   tem,qap,qam,qab,em,d: DOUBLE;
   bz,bpp,bp,bm,az,app: DOUBLE;
   am,aold,ap: DOUBLE;
   m: integer;
BEGIN
   am := 1.0;
   bm := 1.0;
   az := 1.0;
   qab := a+b;
   qap := a+1.0;
   qam := a-1.0;
   bz := 1.0-qab*x/qap;
   FOR m := 1 to itmax DO BEGIN
      em := m;
      tem := em+em;
      d := em*(b-m)*x/((qam+tem)*(a+tem));
      ap := az+d*am;
      bp := bz+d*bm;
      d := -(a+em)*(qab+em)*x/((a+tem)*(qap+tem));
      app := ap+d*az;
      bpp := bp+d*bz;
      aold := az;
      am := ap/bpp;
      bm := bp/bpp;
      az := app/bpp;
      bz := 1.0;
      IF ((abs(az-aold)) < (eps*abs(az))) THEN GOTO 1
   END;
   writeln(outfile,'Error in Statistics calculation');
   {('pause in BETACF');
   writeln('a or b too big, or itmax too small'); readln;}
1:   betacf := az
END;

FUNCTION betai(a,b,x: DOUBLE): DOUBLE;
VAR
   bt: DOUBLE;
BEGIN
   IF ((x < 0.0) OR (x > 1.0)) THEN BEGIN
      writeln(outfile,'Error in Statistics calculation')
      {('pause in routine BETAI'); readln}
   END;
   IF ((x = 0.0) OR (x = 1.0)) THEN bt := 0.0
   ELSE bt := exp(gammln(a+b)-gammln(a)-gammln(b)
           +a*ln(x)+b*ln(1.0-x));
   IF (x < ((a+1.0)/(a+b+2.0))) THEN
      betai := bt*betacf(a,b,x)/a
   ELSE betai := 1.0-bt*betacf(b,a,1.0-x)/b
END;

Begin  {main body of function T-DIST}
  {  Derived from Numerical recipes, Press et al, 1986
   This routine cannot calculate percentiles less than .51 so
     a test for bad values of percentile should be included
     in the option test section if modified to allow limits other than 95%
   Uses a half-step converging routine   (Newton's method)
     to back calculate the value of T
   T to be used here for calculating parametric confidence limits
  }
  PROB := 0.95 * Precision;
   {a T value for two tail 95% confidence limits is being calculated}
  TLAST := 100;
  T := 0.00001;
  TPROB := (1 - betai(DF/2,0.5,DF/(DF+sqr(T))));
       {equation based on two-tailed test}
  REPEAT
    Ttemp := T;
    IF int(Precision*TPROB) > PROB THEN
      T := abs(T - ABS((TLAST - T)/2))
    ELSE T := abs(T + ABS((TLAST - T)/2));
    TPROB := (1 - betai(DF/2,0.5,DF/(DF+sqr(T))));
       {equation based on two-tailed test}
    TLAST := Ttemp;
  UNTIL int(Precision*TPROB) = PROB;
  T_Dist := T
End;  {T_Distribution}

 BEGIN
   WRITELN(outfile);
   WRITELN(outfile,
   '"Bootstrap Estimates of Theoretical Total Species in Community"');
   WRITELN(outfile, '"Number of Estimates" = ', N:4);
   WRITELN(outfile, '"Number of Rejected Data Sets" = ', Num_Rejects:4);
   WRITELN(outfile, ' "Mean total species" = ', (SUM_Sstar/N):9:3);
   Variance := (SUM_Sstar2 - (SQR(SUM_Sstar)/N))/(N-1);
   Standard_Deviation := SQRT(Variance);
   WRITELN(outfile, '           "Variance" = ',Variance:9:3);
   WRITELN(outfile, ' "Standard Deviation" = ', Standard_Deviation:9:3);
   WRITELN(outfile, '      "Minimum value" = ', MIN_Sstar:9:3);
   WRITELN(outfile, '      "Maximum value" = ', MAX_Sstar:9:3);
   t := T_Dist(N-1);
   Interval := t*(sqrt(variance/(N-1)));
   WRITELN(outfile, '"95% Confidence Interval using the t distribution:"');
   WRITELN(outfile, '        "Upper bound" = ', (SUM_Sstar/N) + Interval:9:3);
   WRITELN(outfile, '        "Lower bound" = ', (SUM_Sstar/N) - Interval:9:3);
 END;  {Report_Estimate}

Procedure BOOTSTRAPPER;
    BEGIN
      BOOTING := TRUE;
      WRITELN(outfile);
      WRITELN(outfile,'Now Bootstrapping');
      IF RETRY THEN WRITELN(outfile,
      'Calculated without splitting half of the ones below the veil line.');
      Writeln(outfile);
      IF STATS THEN BEGIN
        WRITELN(outfile,'"Iteration""Estimated"  "Chi-Sq"',
                        '   "Distr"   "Distr"');
        WRITELN(outfile,' "number"  "Total Spp" "Fit Prob"   "Mean',
                          '" "Std Dev" "Entropy" "Evenness"');
       END
       ELSE BEGIN
        WRITELN(outfile,'"Iteration""Estimated"');
        WRITELN(outfile,' "number"  "Total Spp"')
       END;
      IF DATA_OK THEN BEGIN
         Collect_Estimate; {puts original estimate into summation}
         WRITE(outfile, '"orig.est."',TOT_SPECIES:9:3);
         IF STATS THEN WRITE(outfile,'   ',CHIPROB:8:4,
                         '  ',MEAN:8:4,'  ',STDV:8:4,
                         '  ',ENTROPY:8:4,'  ',EVEN:8:4);
         WRITELN(outfile);
      END ELSE
         Num_Rejects := Num_Rejects + 1;
      FOR M := 1 TO Num_Iters DO
        BEGIN
         REPEAT
           DATA_OK := TRUE;
           Make_Pseudo;
           Data_Intervals;
           Describe;
           Analyze;
           IF CHIPROB < 0.005 THEN DATA_OK := FALSE;
           {The filter above has been inserted to reject data sets
            that have extremely poor fits to the lognormal
            distribution.  In general, these data sets will give
            huge areas (numbers of species)
            GW,  modified 30 April 1992, Australian Museum   }
           IF NOT DATA_OK THEN Num_Rejects := Num_Rejects + 1;
           IF Num_Rejects > Num_Iters THEN
             begin
               Writeln(outfile, 'BAD DATA SET: ');
               Writeln(outfile,
               'There are more rejected data sets than iterations requested!');
               Writeln(outfile,'Bootstrapping Halted!');
                 CLOSE(outfile);
               HALT
             end;
         UNTIL DATA_OK;
         Collect_Estimate;
         WRITE(outfile, '   ',M:4,'    ',TOT_SPECIES:9:3);
         IF STATS THEN WRITE(outfile,'   ',CHIPROB:8:4,
                         '  ',MEAN:8:4,'  ',STDV:8:4,
                         '  ',ENTROPY:8:4,'  ',EVEN:8:4);
         WRITELN(outfile);
        END;  {for}
      IF FIRST_OK THEN Num_Iters := Num_Iters + 1;
      Report_Estimate(Num_Iters);
    END; {BOOTSTRAPPER}

BEGIN  {Main Program Body of BOOTLOGN}
  ASSIGN(INFILE, '');   {INPUT REDIRECTION ENABLED}
  RESET(INFILE);
  ASSIGN(outfile, '');  {OUTPUT REDIRECTION ENABLED, SEPARATED FROM OUTPUT}
  REWRITE(outfile);
  Logo;
  Init_Var;
  Get_Data;
  Data_Intervals;
  Describe;
  Analyze;
  RETRY := RETRY AND Try_Again;
  IF RETRY THEN        {this happens if S* < Spp_in_Sample}
    begin              {Retry recalculates without splitting half of the}
      Data_Intervals;  {ones below the veil line}
      Describe;
      Analyze;
    end;
  IF GO_BOOT THEN BOOTSTRAPPER;
  IF TLIST THEN WRITELN(outfile, 'File THEORY.DAT generated');
  CLOSE(INFILE);
  CLOSE(outfile);
  WRITELN(OUTPUT, 'Program Finished');
END.  {program BOOTLOGN}
