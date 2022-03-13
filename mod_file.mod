int T =...; /* עמודות מטריצת מצבת העובדים*/
range year = 1..T; //הגדרת טווחי וסוגי המשתנים
range allyears = 0..T; 
range category=1..T;
range category2=2..T;
int s_input[category,year]=...;
int s0_input[category]=...;
float Pi_junior[category]=...;
float Pi_senior[category]=...;
int CAPi[category]=...;
int TRAINCOSTb=...;
int TRAINCOSTc=...;
int LAYOFFi[category]=...;
int OVERCOSTi[category]=...;
int TEMPCOSTi[category]=...;
int TRAINLIMIT=...;
float TRAINRATIO=...;
float ABAN=...;
int OVERLIMIT=...;
int TEMPLIMIT=...;
float TEMPOUT=...;
range j=1..6; //מספר הצעדים האפשריים ע"י החברה
int K=3; //חלק ג
int M=...;

int MinF=...; /*חלק ב- הוספת תוצאת חלק א כנתון*/

dvar int+ C; /*חלק ב-מטרה החלטה עלות*/
dvar boolean x[j,year];

dvar int+ R[category,allyears]; /* גיוס עובדים */
dvar int+ PB[year];        /* הכשרה מB ל-A*/
dvar int+ PC[year];        /* הכשרה מC ל-B*/
dvar int+ DA[category2,year]; /*שנמוך מ-A*/
dvar int+ DB[year];         /*שנמוך מ-B*/
dvar int+ F[category,year]; /* מפוטרים */
dvar int+ O[category,year]; /* העסקת יתר */
dvar int+ TW[category,year]; /* גיוס עובדים זמניים */
dvar int+ CUR[category,allyears]; /* פונקציית עזר לחישוב מצבת עובדים  */

 
//minimize sum(i in category,t in year) F[i,t]; /*חלק א - פונקצית המטרה*/
minimize C;/* חלק ב-פונקצית המטרה*/
subject to {
 
 //the following constraints are for part GIMEL//
 forall (t in year) sum(i in category)R[i,t]<=M*x[1,t]; ////גיוס
 forall (t in year) PB[t]<=M*x[2,t]; //promotion from B to A
 forall (t in year) PC[t]<=M*x[2,t]; //promotion from C to B
 forall (t in year) sum(i in category2)DA[i,t]<=M*x[3,t]; //downgrade from A to either B or C
 forall (t in year) DB[t]<=M*x[3,t]; //downgrade from B
 forall (t in year) sum(i in category) F[i,t]<=M*x[4,t]; //fired employees
 forall (t in year) sum(i in category)O[i,t]<=M*x[5,t]; //overlimit employees
 forall (t in year) sum(i in category)TW[i,t]<=M*x[6,t]; //temporary workers
    
 forall (t in year) sum(steps in j) x[steps,t]<=K; 
 //
 
 //the following constraints are relevant for all parts of the project//
 forall (i in category) R[i,0]==0; //אתחול גיוס שנת 0
 
 forall (i in category,t in year) R[i,t] <= CAPi[i]; //* מגבלת גיוס   *//

 forall (t in year) PC[t] <= TRAINLIMIT;  //* הכשרה מC ל-B*//
 forall (t in year) PB[t] <= (CUR[2,t]+PB[t])*TRAINRATIO;  //הכשרה מB ל-A*//
 
 forall (i in category, t in year) CUR[i,t]+TW[i,t]*TEMPOUT>=s_input[i,t]; // עמידה בתחזית*//
 
 forall (t in year) CUR[2,t]-R[2,t]+PB[t]-PC[t]*(1-Pi_senior[2]) >= PB[t];//.עובדים המגוייסים בתקופה מסויימת לא יכולים לצאת להכשרה באותה התקופה// change
 forall (t in year) CUR[3,t]-R[3,t]+PC[t] >= PC[t];//עובדים המגוייסים בתקופה מסויימת לא יכולים לצאת להכשרה באותה התקופה//
  
 forall (i in category,t in year) O[i,t]==CUR[i,t]-s_input[i,t]; //* הגדרת העסקת יתר   *//
 forall (t in year) sum(i in category) O[i,t] <= OVERLIMIT; //*מגבלת העסקת יתר בכלל החברה  *//
 
 forall (i in category,t in year) TW[i,t]<=TEMPLIMIT; //*מגבלת העסקת עובדים זמנייים  *//
 
 forall (i in category) CUR[i,0]==s0_input[i]; //הגדרת תנאי ההתחלה של מצבת העובדים - שנת 0//
 
 forall (t in year) CUR[3,t]== CUR[3,t-1]*(1-Pi_senior[3])+(DB[t]+DA[3,t])*(1-ABAN)+R[3,t]*(1-Pi_junior[3])-PC[t]-F[3,t]; //* פונקציית עזר לחישוב עובדים בכל תקופה בקטגוריה C*//

 forall (t in year) CUR[2,t]== CUR[2,t-1]*(1-Pi_senior[2])+DA[2,t]*(1-ABAN)+R[2,t]*(1-Pi_junior[2])+PC[t]*(1-Pi_senior[2])-PB[t]-DB[t]-F[2,t]; // פונקציית עזר לחישוב עובדים בכל תקופה בקטגוריה B*// 
 
 forall (t in year) CUR[1,t]== CUR[1,t-1]*(1-Pi_senior[1])+R[1,t]*(1-Pi_junior[1])+PB[t]*(1-Pi_senior[1])-DA[2,t]-DA[3,t]-F[1,t]; //* פונקציית עזר לחישוב עובדים בכל תקופה בקטגוריה A*// 
 
 //the following constraints are relevant for part BEIT//
 sum(i in category,t in year)F[i,t]<=MinF; /*חלק ב-הוספת אילוץ המפוטרים*/
 
 C==TRAINCOSTc*(sum(t in year)PC[t])+(TRAINCOSTb*(sum(t in year)PB[t]))+sum(i in category)LAYOFFi[i]*(sum(t in year)F[i,t])
+sum(i in category)OVERCOSTi[i]*(sum (t in year)O[i,t])+sum(i in category)TEMPCOSTi[i]*(sum (t in year)TW[i,t]); /*חלק ב-הגדרת עלויות החברה*/
//
 }