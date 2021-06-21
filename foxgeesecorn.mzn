int: f; % foxes
int: g; % geese
int: c; % corn
int: k; % max objects on boat
set of int: Cap = 0..k;
int: t; % max number of trips
set of int: Trips = 1..t;
int: pf; % fox price
int: pg; % goose price
int: pc; % corn price

set of int: ValueRange = 0..f*pf + g*pg + c*pc;

var Trips: trips; % number of actual trips

% Number of items taken on each trips
array[Trips] of var Cap: foxes;
array[Trips] of var Cap: geese;
array[Trips] of var Cap: corn;

% Number of items on west side after each trip
array[Trips] of var 0..f: foxesWest;
array[Trips] of var 0..g: geeseWest;
array[Trips] of var 0..c: cornWest;

% Number of items on east side after each trip
array[Trips] of var 0..f: foxesEast;
array[Trips] of var 0..g: geeseEast;
array[Trips] of var 0..c: cornEast;

% Number of dead items after each trip
array[Trips] of var 0..f: foxesDead;
array[Trips] of var 0..g: geeseDead;
array[Trips] of var 0..c: cornDead;

function var ValueRange: value(var int: i) =
  pf*foxesEast[i] + pg*geeseEast[i] + pc*cornEast[i];

% Death conditions
function var 0..1: foxLosses(var int: nf, var int: ng, var int: nc) =
  if nf != 0 /\ ng = 0 /\ nc != 0 then 1
  elseif nf != 0 /\ ng != 0 then if nf > ng then 1 else 0 endif
  else 0 endif;

function var 0..f: geeseLosses(var int: nf, var int: ng, var int: nc) =
  if nf != 0 /\ ng != 0 then if nf <= ng then nf else 0 endif
  elseif nf = 0 /\ ng != 0 /\ nc != 0 /\ ng > nc then 1
  else 0 endif;

function var 0..g: cornLosses(var int: nf, var int: ng, var int: nc) =
  if nf != 0 /\ ng = 0 /\ nc != 0 then 1
  elseif nf = 0 /\ ng != 0 /\ nc != 0 then if ng <= nc then ng else 1 endif
  else 0 endif;

% Items on the west side after the first trip
constraint
  let {
    var 0..f: nf = f - foxes[1];
    var 0..g: ng = g - geese[1];
    var 0..c: nc = c - corn[1];
  } in
  foxesWest[1] = nf - foxLosses(nf, ng, nc) /\
  geeseWest[1] = ng - geeseLosses(nf, ng, nc) /\
  cornWest[1] = nc - cornLosses(nf, ng, nc) /\
  foxesDead[1] = foxLosses(nf, ng, nc) /\
  geeseDead[1] = geeseLosses(nf, ng, nc) /\
  cornDead[1] = cornLosses(nf, ng, nc);

% Items on the east side after the first trip
constraint foxesEast[1] = foxes[1];
constraint geeseEast[1] = geese[1];
constraint cornEast[1] = corn[1];

% Boat can carry up to k items
constraint forall (i in 1..trips) (foxes[i] + geese[i] + corn[i] <= k);

% West -> East
constraint forall (i in 3..trips where i mod 2 = 1) (
  let {
    var 0..f: nf = foxesWest[i-1] - foxes[i];
    var 0..g: ng = geeseWest[i-1] - geese[i];
    var 0..c: nc = cornWest[i-1] - corn[i];
  } in
  foxesDead[i] = foxLosses(nf, ng, nc) /\
  foxesWest[i] = nf - foxesDead[i] /\
  foxesEast[i] = foxesEast[i-1] + foxes[i] /\

  geeseDead[i] = geeseLosses(nf, ng, nc) /\
  geeseWest[i] = ng - geeseDead[i] /\
  geeseEast[i] = geeseEast[i-1] + geese[i] /\

  cornDead[i] = cornLosses(nf, ng, nc) /\
  cornWest[i] = nc - cornDead[i] /\
  cornEast[i] = cornEast[i-1] + corn[i] /\

  % There will either be a geese or a corn massacre, or neither
  geeseDead[i] + cornDead[i] <= max(nf, ng));

% East -> West
constraint forall (i in 2..trips where i mod 2 = 0) (
  let {
    var 0..f: nf = foxesEast[i-1] - foxes[i];
    var 0..g: ng = geeseEast[i-1] - geese[i];
    var 0..c: nc = cornEast[i-1] - corn[i];
  } in
  foxesDead[i] = foxLosses(nf, ng, nc) /\
  foxesEast[i] = nf - foxesDead[i] /\
  foxesWest[i] = foxesWest[i-1] + foxes[i] /\

  geeseDead[i] = geeseLosses(nf, ng, nc) /\
  geeseEast[i] = ng - geeseDead[i] /\
  geeseWest[i] = geeseWest[i-1] + geese[i] /\

  cornDead[i] = cornLosses(nf, ng, nc) /\
  cornEast[i] = nc - cornDead[i] /\
  cornWest[i] = cornWest[i-1] + corn[i] /\

  % There will either be a geese or a corn massacre, or neither
  geeseDead[i] + cornDead[i] <= max(nf, ng));

% The number of trips is odd
constraint trips mod 2 = 1;

% Should move something in the first trip
constraint not (foxes[1] = 0 /\ geese[1] = 0 /\ corn[1] = 0);

% Stop if there are no more items on the west side
constraint forall (i in 1..trips-1) (
  not (foxesWest[i] = 0 /\ geeseWest[i] = 0 /\ cornWest[i] = 0));

% Should not move back the exact same items as last trip
constraint forall (i in 2..trips where i mod 2 = 0) (
  not (foxes[i] = foxes[i-1] /\ geese[i] = geese[i-1] /\ corn[i] = corn[i-1]));

% Items can only decrease in number
constraint forall (i in 2..trips) (
  foxesWest[i] + foxesEast[i] <= foxesWest[i-1] + foxesEast[i-1] /\
  geeseWest[i] + geeseEast[i] <= geeseWest[i-1] + geeseEast[i-1] /\
  cornWest[i] + cornEast[i] <= cornWest[i-1] + cornEast[i-1]);

% Alive + dead = All
constraint forall (i in 1..trips) (
  foxesWest[i] + foxesEast[i] + sum([foxesDead[j] | j in 1..i]) = f /\
  geeseWest[i] + geeseEast[i] + sum([geeseDead[j] | j in 1..i]) = g /\
  cornWest[i] + cornEast[i] + sum([cornDead[j] | j in 1..i]) = c);

% Upper bound for number of items possible to transfer in time
constraint foxesEast[trips] <= k * trips div 2;
constraint geeseEast[trips] <= k * trips div 2;
constraint cornEast[trips] <= k * trips div 2;

var ValueRange: obj = value(trips);
solve :: int_search([trips], input_order, indomain_min, complete) maximize obj;

output
["fox = ", show(foxes), ";\n"] ++
["geese = ", show(geese), ";\n"] ++
["corn  = ", show(corn), ";\n"]  ++
["trips = ", show(trips), ";\n"] ++
["obj   = ", show(obj), ";\n"];
