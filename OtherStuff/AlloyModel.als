sig Integer {}

sig Strings {}

sig Date {}

sig Status {}

sig Time {}

sig Gender {}

sig Coordinate{}

abstract sig User {}

sig Guest extends User {
}

sig Admin extends User{
  name: one Strings,
  surname: one Strings
}

abstract sig RegUser extends User{
  name: one Strings,
  surname: one Strings
}

sig Customer extends RegUser{
  gender: one Gender,
  birth: one Date,
  email: one Strings,
  telephone: one Strings
}

sig TaxiDriver extends RegUser{
  status: one Status,
  taxi: one Taxi
}

sig Taxi {
  code: one Integer
  position: one Coordinate
}

sig TaxiQueue {
  queue: set Taxi
}

sig TaxiZone {
  taxiQueue: one TaxiQueue
}

sig Map {
  zone: some TaxiZone
}

sig System {
  map: one Map
  users: set Users
  taxiRide: set TaxiRide
}

abstract sig TaxiRide {
  origin: one Coordinate,
  destination: one Coordinate,
  waitingTime: lone Integer,
  code: lone Integer,
  taxi: lone Taxi
}

sig Request extends TaxiRide {
  
}

sig Reservation extends TaxiRide {
  date: one Date,
  time: one Time
}

pred show {}
