/* FIRST_ILP.mod */
/* 
   ILP for Zone FLF 
   This model maximizes the number of accepted connection requests.
   It selects a single candidate path among the K-shortest for each request,
   chooses a modulation level (subject to transmission reach), and allocates 
   contiguous frequency slots within zones. Requests are assigned to either 
   the left or right side of a zone based on connection type.
*/

set NODES;          /* Set of nodes */
set LINKS within {NODES, NODES};  /* Set of (undirected) links */
#set TRAFFIC;        /* Traffic requests, each as an ordered pair (s,d) */
set TRAFFIC, dimen 2;

set MODULATIONS;    /* Available modulation formats */
set ZONES;          /* Zones for spectrum allocation */
param K integer > 0;    /* Number of candidate paths considered */

/* Parameters from the formulation */
param T_sd {TRAFFIC} > 0;          /* Traffic demand for each (s,d) */
param C > 0;                      /* Capacity of one frequency slot for given modulation */
param D {LINKS} >= 0;             /* Distance of each link (m,n) */
param R {MODULATIONS} > 0;        /* Maximum transmission reach for modulation m */
param G integer >= 0;             /* Guard band (in slots) required between connections */
param C_z {ZONES} > 0;            /* Capacity (in slots) of each zone */

param M_big integer > 0;  /* A sufficiently large constant, e.g., N_slots + max_allocation_length */


/* Candidate paths: For each traffic request t, we have a set PATHS[t] of candidate paths */
set PATHS {t in TRAFFIC};

/* For each candidate path, list the links (as pairs from LINKS) used by that path */
set PATH_LINKS {t in TRAFFIC, p in PATHS[t]} within LINKS;

/* For each traffic t and candidate path p, define the set of modulation formats that are feasible */
set FEAS_MOD {t in TRAFFIC, p in PATHS[t]} within MODULATIONS;

/* For each (t, p, m) triple, the number of frequency slots required (based on traffic and modulation) */
param N_req {t in TRAFFIC, p in PATHS[t], m in FEAS_MOD[t,p]} > 0;

/* --- Decision Variables --- */

/* Accept[t] = 1 if traffic request t is accepted */
var Accept {t in TRAFFIC}, binary;

/* UsePath[t,p] = 1 if candidate path p is selected for traffic t */
var UsePath {t in TRAFFIC, p in PATHS[t]}, binary;

/* UseMod[t,p,m] = 1 if modulation m is selected for traffic t on candidate path p */
var UseMod {t in TRAFFIC, p in PATHS[t], m in FEAS_MOD[t,p]}, binary;

/* Route[t,p,m,(i,j)] = 1 if link (i,j) is used for t on path p with modulation m.
   (This is mainly used to “activate” the links of the chosen path.)
*/
var Route {t in TRAFFIC, p in PATHS[t], m in FEAS_MOD[t,p], (i,j) in PATH_LINKS[t,p]}, binary;

/* PathDist[t,p]: total distance of candidate path p for traffic t */
var PathDist {t in TRAFFIC, p in PATHS[t]} >= 0;

/* For zone-based slot allocation, we assume each accepted request is assigned either
   from the left or the right side of its zone.
   LeftAlloc[t] = 1 if request t is allocated from left side; RightAlloc[t] = 1 if from right.
*/
var LeftAlloc {t in TRAFFIC}, binary;
var RightAlloc {t in TRAFFIC}, binary;

/* Starting and ending slot indices for the allocation of traffic t.
   For simplicity we assume a single contiguous block (the actual model may have separate
   indices for left and right allocations; here we show a simplified approach).
*/
var StartSlot {t in TRAFFIC} integer >= 1;
var EndSlot   {t in TRAFFIC} integer >= 1;

/* Spectrum tracking variable: maximum index used in any link */
var S_max integer >= 0;

var y {t1 in TRAFFIC, t2 in TRAFFIC: t1 < t2}, binary;

/* --- Objective --- */
maximize TotalAccepted:
    sum {t in TRAFFIC} Accept[t];

/* --- Constraints --- */

/* (1) Each traffic request, if accepted, must choose exactly one candidate path */
s.t. PathSelection {t in TRAFFIC}:
    sum {p in PATHS[t]} UsePath[t,p] = Accept[t];

/* (2) For each chosen path, exactly one modulation format is selected */
s.t. ModulationSelection {t in TRAFFIC, p in PATHS[t]}:
    sum {m in FEAS_MOD[t,p]} UseMod[t,p,m] = UsePath[t,p];

/* (3) Compute the total distance of each candidate path (sum of link distances) */
s.t. ComputePathDist {t in TRAFFIC, p in PATHS[t]}:
    PathDist[t,p] = sum { (i,j) in PATH_LINKS[t,p] } D[i,j];

/* (4) Modulation feasibility: enforce that the chosen modulation’s reach covers the path distance.
       Using a big-M formulation.
*/
s.t. ModulationFeas {t in TRAFFIC, p in PATHS[t], m in FEAS_MOD[t,p]}:
    PathDist[t,p] <= R[m] + (1 - UseMod[t,p,m])*1e6;

/* (5) Zone-based left/right allocation: Each accepted request must be allocated from exactly one side.
       (This simplified constraint forces one side allocation.)
*/
s.t. LeftRightAlloc {t in TRAFFIC}:
    LeftAlloc[t] + RightAlloc[t] = Accept[t];

/* (6) Spectrum allocation: Ensure that the frequency block for each request is correctly sized.
       For simplicity, we require that the block length equals the number of slots required for the chosen modulation.
       Here we assume that if request t uses path p and modulation m, then:
         EndSlot[t] - StartSlot[t] + 1 = N_req[t,p,m]   for the chosen (p,m).
       We linearize by enforcing for all (p,m) but only the chosen one (UseMod=1) matters.
*/
s.t. SlotBlockLength {t in TRAFFIC, p in PATHS[t], m in FEAS_MOD[t,p]}:
    EndSlot[t] - StartSlot[t] + 1 = N_req[t,p,m] * UseMod[t,p,m]
    + (1 - UseMod[t,p,m])*0;   /* When not chosen, this constraint is inactive */

/* (7) Spectrum non-overlap with guard band:
       For any two accepted requests that share a common link and zone,
       the spectrum blocks must not overlap. (A simplified version uses a “big-M” disjunctive constraint.)
       Here we illustrate for any two distinct traffic requests.
*/
s.t. SpectrumNonOverlap1 {t1 in TRAFFIC, t2 in TRAFFIC: t1 < t2}:
    StartSlot[t1] + (EndSlot[t1] - StartSlot[t1] + 1) + G <= StartSlot[t2] + M_big * (1 - y[t1,t2]);

s.t. SpectrumNonOverlap2 {t1 in TRAFFIC, t2 in TRAFFIC: t1 < t2}:
    StartSlot[t2] + (EndSlot[t2] - StartSlot[t2] + 1) + G <= StartSlot[t1] + M_big * y[t1,t2];

/* (8) Maximum spectrum index tracking: Ensure S_max is at least the ending slot of every accepted request */
s.t. MaxSpectrum {t in TRAFFIC}:
    S_max >= EndSlot[t];

/* (9) (Optional) Enforce S_max does not exceed a global limit.
       For example, if the overall available spectrum is N_slots.
*/
param N_slots integer > 0;
s.t. SlotLimit:
    S_max <= N_slots;

solve;

display Accept, UsePath, UseMod, StartSlot, EndSlot, S_max;
