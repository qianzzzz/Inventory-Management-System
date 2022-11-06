/*********************************************
 * OPL 20.1.0.0 Model
 * Author: zhaoqian
 * Creation Date: May 10, 2022 at 1:37:16 PM
 *********************************************/
 using CP;
 execute {
   cp.param.TimeLimit = 60;
 }

 int T = ...; // horizon
 int N = ...; // shelf-life
 int Q = ...; // lot-size
 int h = ...;
 int K = ...;
 int d[1..T] = ...;
 int init[1..N] = ...; // remaining shelf-life 1,2,..
 int c = ...; // unit cost
 int s = ...; // normal selling price
 int smin = c; // min selling price
 float elast = ...; // price elasticity of demand
 
 dvar int+ p[1..T] in smin..s; // discounted price, irrespective of shelf-life
 dvar int+ order[1..T] in 0..1; // place an order
 dvar int+ L[1..T]; // # of lots
 dvar int+ preinv[1..T,1..N]; // opening (pre-order) stock level
 dvar int+ postinv[1..T,1..N]; // opening (post-order) stock level
 dvar int+ closeinv[1..T,0..N-1]; // closing stock level
 dvar int+ induced_d[1..T]; // induced demand
 dvar int+ alpha[1..T,1..N] in 0..1;
 dvar int+ beta[1..T,1..N] in 0..1;
 dvar int+ profit;
 
 maximize profit;
 subject to {      
   profit == sum(t in 1..T) (p[t]*induced_d[t] - K*order[t] - h*sum(n in 0..N-1) closeinv[t,n] - c*Q*L[t]);
   
   forall(n in 1..N) preinv[1,n] == init[n]; // 1st period
   forall(t in 2..T) preinv[t,N] == 0; // periods 2..T
   forall(t in 1..T,n in 1..N-1) postinv[t,n] == preinv[t,n]; // remaining shelf-life 1..N-1
   forall(t in 1..T) postinv[t,N] == Q*L[t]; // fresh products
   
   forall(t in 1..T) induced_d[t] == d[t] + ceil(elast*d[t]*(s-p[t]));
   // for today's order we want to make sure it will not go exceed the future rest of planning days summing demand, the upper limit is to cover all      
   forall(t in 1..T) Q*L[t] <= sum(i in t..T) induced_d[t]*order[t];
//   forall(t in 1..T) Q*L[t] <= induced_d[t]*order[t];

   forall(t in 1..T-1,n in 1..N-1) closeinv[t,n] == preinv[t+1,n];

   forall(t in 1..T,n in 1..N-1) alpha[t,n] >= alpha[t,n+1]; // FIFO
   forall(t in 1..T,n in 1..N-1) beta[t,n] >= beta[t,n+1];
   forall(t in 1..T) induced_d[t] <= sum(n in 1..N) alpha[t,n]*postinv[t,n];  
   forall(t in 1..T) induced_d[t] >= sum(n in 1..N) beta[t,n]*postinv[t,n];  
   forall(t in 1..T) sum(n in 1..N) alpha[t,n] - sum(n in 1..N) beta[t,n] == 1;
   forall(t in 1..T)
     forall(n in 1..N) {
       closeinv[t,n-1] >= (1-alpha[t,n])*postinv[t,n];
       closeinv[t,n-1] <= (1-beta[t,n])*postinv[t,n];
     };

   forall(t in 1..T)
     sum(n in 0..N-1) closeinv[t,n] == sum(n in 1..N) postinv[t,n] - induced_d[t];
     
};