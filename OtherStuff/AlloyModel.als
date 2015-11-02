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
  rideStatus: one RideStatus,
  hasCustomer: one Customer
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
  no disj r1,r2:TaxiRide | (r1.rideStatus = r2.rideStatus) and (r2.rideStatus = Assigned) and 
																(r1.hasCustomer = r2.hasCustomer) 
  no disj r1,r2:Request | (r1.rideStatus = r2.rideStatus) and (r2.rideStatus = NotAssigned) and 
																(r1.hasCustomer = r2.hasCustomer)
  no disj r1,r2:Request | (r1.rideStatus = Assigned) and (r2.rideStatus = NotAssigned) and
																(r1.hasCustomer = r2.hasCustomer)
  no disj r1:Request, r2:Reservation| (r1.rideStatus = NotAssigned) and (r2.rideStatus = Assigned) and
																(r1.hasCustomer = r2.hasCustomer)
}

//taxi (or taxi driver) has no more than 1 taxiRide with assigned status
fact driverOneRide{
  no disj r1,r2:TaxiRide | (r1.taxi = r2.taxi) and (r1.rideStatus = Assigned) and (r2.rideStatus = r1.rideStatus)
}

//no taxi paired with a taxi ride with "not assigned" status
fact noTaxiNotAssigned{
  all r1:TaxiRide | (r1.rideStatus = NotAssigned) implies (r1.taxi = none)
}

fact TaxiRideStatus{
    all r1:TaxiRide | (r1.rideStatus != NotAssigned) implies (#r1.taxi=1)
}

fact numberEq{
  #System.users = # User
  #System.taxiRide = #TaxiRide
}

//busy taxi must not be in a queue
fact taxiBusyQueue{
  all d1:TaxiDriver | ((d1.status = Busy) implies (no q1:TaxiQueue | d1.taxi  in  q1.hasTaxi))
}

//available taxi must be in a queue
fact taxiAvailableQueue{
  all d1:TaxiDriver | ((d1.status = Available) implies (some q1:TaxiQueue | d1.taxi  in  q1.hasTaxi))
}

//Assertions

assert numbersEquivalence{
  #Taxi = #TaxiDriver
  #TaxiZone = #hasTaxiQueue
  #System.users = # User
  #System.taxiRide = #TaxiRide
}

//

//Origin cannot be equal to destination

//check numbersEquivalence

//Other commands

pred addAssignedRide(s1:System, r1:TaxiRide){
  ((r1 not in s1.taxiRide) implies (s1.taxiRide = s1.taxiRide + r1)) and  r1.rideStatus = Assigned
}

run addAssignedRide for 10 but 10 Taxi

pred show {

}

run show for 3 but 10 Taxi
