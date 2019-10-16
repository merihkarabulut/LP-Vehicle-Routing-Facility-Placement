range Nodes = 1..8;
range Sources = 1..2;
range Targets = 7..8;
range OtherNodes = 3..6;
range Trucks = 1..20;

int M = 99999999999; // Big M

int Distance[Nodes][Nodes] = ...;

int EdgeExists[Nodes][Nodes] = ...;
int UnloadPermission[Nodes] = ...;
int LoadPermission[Nodes] = ...;

int Demand[Nodes] = ...;
int Production[Nodes] = ...;

//Costs
float CostDrive = 0.0625;    //euros per km, cost of driving the truck
int OpenFacilityCost = 10000; //euros per charging station
int TruckProcurement = 100; // euros per truck in use


int BatteryCap = 90; //km
int TruckCap = 300; //kg



//Decision Variables
dvar boolean X[Nodes][Nodes][Trucks];  //boolean variable indicates whether the truck t drives from i to j or not.
dvar int Unloaded[Nodes][Trucks]; //the amount that truck t unloads at node i.
dvar int TotalUnloaded[Nodes];    // dummy decision variable, to easily check the total amount unloaded at node i.

dvar int Loaded[Nodes][Trucks]; //the amount that truck t is loaded at node i.
dvar int TotalLoaded[Nodes];   // dummy decision variable, to easily check the total amount loaded at node i.
dvar boolean TruckInUse[Trucks]; //whether the truck t is used or not.

dvar boolean Y[Nodes]; //whether node i has a charging station or not. 


//BATTERY RELATED DECISION VARIABLES!!!
dvar int q[Nodes][Nodes][Trucks];




//there is no mismatch demand, also we realize that the no-solution scenarios can exist due to the battery capacity and distance.
// however, we assume that the distances are always lower than a truck's battery capacity, this can also be considered in a way that
//we use such a grid which provides with the sufficient candidate recharging points so that we can always reach the destinations by using
//the stations or not. 

//Objective Function
dexpr float TransportationCost = (sum(i in Nodes) sum(j in Nodes) sum(t in Trucks) X[i][j][t]*(CostDrive*Distance[i][j]) + sum(t in Trucks)TruckInUse[t]*TruckProcurement);
dexpr float FacilityOpeningCost = sum(i in Nodes) Y[i] * OpenFacilityCost;

minimize TransportationCost + FacilityOpeningCost - OpenFacilityCost*2;







subject to{


//if edge does not exist, then truck cannot use it.
forall(t in Trucks)
  forall(i in Nodes)
    forall(j in Nodes)
      X[i][j][t] <= EdgeExists[i][j];

//source node degree constraint
forall(t in Trucks)
  forall(s in Sources)
    sum(i in OtherNodes)X[s][i][t] <= 1;

//To eliminate the situations in which the same truck teleports from a destination to another source and carries goods again. 
//the total number of departures from sources has to be <= 1 for a truck t.
forall(t in Trucks)
  sum(s in Sources)sum(o in OtherNodes)X[s][o][t] <= 1;
    

//target node degree constraints
forall(t in Trucks)
  forall(d in Targets)
    sum(i in OtherNodes) X[i][d][t] <= 1;
    
//truck inflow = truck outflow for each node.
forall(t in Trucks)
  forall(i in OtherNodes)
    sum(j in Nodes) X[i][j][t] == sum(j in Nodes) X[j][i][t];

//a truck has to arrive to a target by departing from an "othernode" (IF that truck is already started its movement from a source).
forall(t in Trucks)
    sum(i in OtherNodes) (sum(d in Targets) X[i][d][t]) >= sum(s in Sources)(sum(o in OtherNodes)X[s][o][t]);

//if there is a demand, then (demand/capacity of trucks) triggers the amount of trucks that we want to use
// has to leave the sources and go to an "othernode".
sum(t in Trucks)(sum(s in Sources)(sum(o in OtherNodes)X[s][o][t])) >= (sum(i in Nodes)Demand[i])/TruckCap;

//If a truck is being used on the i-j edge, then its indicator should be updated.
forall(t in Trucks)
  forall(i in Nodes)
    forall(j in Nodes)
      TruckInUse[t] >= X[i][j][t];
      
      
      


//dummy equation to control the total amount unloaded.
forall(i in Nodes)
  sum(t in Trucks) Unloaded[i][t] == TotalUnloaded[i];
  
//dummy equation to control the total amount loaded.
forall(i in Nodes)
  sum(t in Trucks) Loaded[i][t] == TotalLoaded[i];





//Truck t cannot unload more than it has been loaded
forall(t in Trucks)
  sum(i in Nodes) Unloaded[i][t] <= sum(i in Nodes) Loaded[i][t];

//Satisfy the demand!
//WE CAN OMIT THIS CONSTRAINT AND HAVE THE NOTION OF MISMATCHED DEMAND !!!
//however, for now, starting with the fixed and sufficient amount of trucks seemed useful to me.
//due to the procurement cost, the model does not use unnecessary trucks anyways.
forall(i in Nodes)
  TotalUnloaded[i] == Demand[i];

//only targets can unload
//added this constraint since there is no cost identified for loading and unloading process
//and a truck can easily can be loaded excessively, and this truck can unload this excessive part in random places where it visits
//the solution does not get affected from this process, but it is meaningless. I just wanted to eliminate this possibility.
forall(i in Nodes)
  forall(t in Trucks)
    Unloaded[i][t] <= UnloadPermission[i] * M;

//Truck t can unload at node i only if it visits there.
forall(i in Nodes)
  forall(t in Trucks)
    Unloaded[i][t] <= sum(j in Nodes) X[j][i][t] * M;

//Truck t can get its load at node i only if it visits there.
forall(i in Nodes)
  forall(t in Trucks)
    Loaded[i][t] <= sum(j in Nodes) X[i][j][t] * M;
    
//Truck capacity constraint
forall(t in Trucks)
  sum(i in Nodes) Loaded[i][t] <= TruckCap;

//Production capacity constraint
forall(i in Nodes)
  sum(t in Trucks)Loaded[i][t] <= Production[i];



//BATTERY CAPACITY & RECHARGING & TOTAL DISTANCE CONSTRAINTS

forall(i in Sources)
  Y[i] == 1;

forall(j in Nodes)
  forall(i in Nodes)
    forall(t in Trucks)
      q[i][j][t] <= X[i][j][t] * M;

forall(i in Nodes)
  forall(t in Trucks)
    sum(j in Nodes)q[i][j][t] <= sum(z in Nodes)q[z][i][t] - (sum(j in Nodes)(X[i][j][t] * Distance[i][j])) + (Y[i]*M);
      
forall(i in Nodes)
  forall(t in Trucks)
    sum(j in Nodes)q[i][j][t] <= Y[i]*BatteryCap - sum(j in Nodes)X[i][j][t]*Distance[i][j] + (1-Y[i])*M;

forall(j in Nodes)
  forall(i in Nodes)
    forall(t in Trucks)
      q[i][j][t] <= BatteryCap;

//non negativity constraints
forall(j in Nodes)
  forall(i in Nodes)
    forall(t in Trucks)
      q[i][j][t] >= 0;

forall(i in Nodes)
  forall(t in Trucks)
    Unloaded[i][t] >= 0;

forall(i in Nodes)
  forall(t in Trucks)
    Loaded[i][t] >= 0;
}