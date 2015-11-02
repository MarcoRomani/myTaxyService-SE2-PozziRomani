//****Signatures 

sig Integer {}

sig Strings {}

sig Date {}

enum DriverStatus {Busy, Available}

enum RideStatus{Annulled, Assigned, Completed, NotAssigned}

sig Time {}

sig Coordinate{}

abstract sig User {}

sig Guest extends User {}

sig Admin extends User{
  name: one Strings,
  surname: one Strings,
  email: one Strings,
  password: one Strings
}

abstract sig RegUser extends User{
  name: one Strings,
  surname: one Strings,
  password: one Strings
}

sig Customer extends RegUser{
  birth: one Date,
  email: one Strings,
  telephone: one Strings
}

sig TaxiDriver extends RegUser{
  status: one DriverStatus,
  taxi: one Taxi
}

sig Taxi {
  code: one Integer,
  position: one Coordinate
}

sig TaxiQueue {
  hasTaxi: set Taxi
}

sig TaxiZone {
  hasTaxiQueue: one TaxiQueue
}

one sig Map {
  hasZone: some TaxiZone
}

one sig System {
  map: one Map,
  users: set User,
  taxiRide: set TaxiRide
}

abstract sig TaxiRide {
  origin: one Coordinate,
  destination: lone Coordinate,
  date: one Date,
  time: one Time,
  waitingTime: lone Integer,
  taxi: lone Taxi,
  rideStatus: one RideStatus
}

sig Request extends TaxiRide {
  
}

sig Reservation extends TaxiRide {

}
//****Facts

//No duplicate users
fact noDuplicateUsers{
  no disj u1,u2:RegUser | (u1.email = u2.email) or (u1.telephone = u2.telephone)
  no disj a1,a2:Admin | (a1.email = a2.email)
  no disj a1:Admin, u1:RegUser | (a1.email = u1.email)
}

//Every taxi has always exactly one driver
fact taxiOneDriver{
  //#Taxi = #TaxiDriver
  TaxiDriver <: taxi in TaxiDriver one->Taxi
}

//Every taxi queue has always exactly one taxi zone
fact queueOneZone{
  TaxiZone <: hasTaxiQueue in TaxiZone one -> TaxiQueue
}

//Every taxi can be in only one queue
fact taxiOneQueue{
  no disj q1,q2:TaxiQueue | (q1.hasTaxi = q2.hasTaxi)
}

fact taxiZoneInMap{
  TaxiZone in Map.hasZone
}

//No more than 1 "Assigned" taxiRide for customer
fact RideLimit{
  no disj r1,r2:TaxiRide,  | (r1.
}

fact numberEq{
  #System.users = # User
  #System.taxiRide = #TaxiRide
}


//Assertions

assert numbersEquivalence{
  #Taxi = #TaxiDriver
  #TaxiZone = #hasTaxiQueue
  #System.users = # User
  #System.taxiRide = #TaxiRide
}

//Origin cannot be equal to destination

//check numbersEquivalence

//Other commands

pred show {}

run show for 3 but 3 TaxiZone
