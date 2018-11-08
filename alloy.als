open util/time
open util/integer
open util/boolean

-- SIGNATURES

sig User {
	name: one String,
	partyList: set ThirdParty,
	age: one Int,
	ssn: one String,
	email: one String,
	phoneNumber: one String,
	sos: one Bool, -- 1 if the User is registered to AutomatedSOS, 0 otherwise
	location: Location,
	healthStatus: one Int --if status is negative, the User is automatically assisted by ambulance
}

sig ThirdParty {
	name: one String,
	ssn: one String,
	accessibleUser: set User,
	subbedTo: set User,
	sampling: set Sampling
} {
	all u: User, p: ThirdParty  | u in subbedTo implies u in accessibleUser and p in u.partyList iff u in accessibleUser 
}

sig Ambulance {
	id: one String,
	available: one Bool, -- 0 available, 1 not available
	location: Location
}

abstract sig Device{}
one sig Smartphone extends Device{}
one sig Smartwatch extends Device{}

sig Location {
	longitude: one Int,
	latitude: one Int
}

sig LocationTracker {
	user: User, 
	location: Location
}

abstract sig AssistanceStatus{}
one sig Started extends AssistanceStatus{}
one sig Finished extends AssistanceStatus{}

sig Assistance {
	user: User,
	elapsedTime: one Int,
	assistanceStatus: lone AssistanceStatus
} {
	elapsedTime >= 0
}

one sig AutomatedSOS {
	assistances: set Assistance
}
	
sig Sampling {
	users: set User,
	valid: one Bool
}


-- FACTS 

fact userIsUnique {
	no disjoint user1, user2: User | user1.ssn = user2.ssn and user1.email = user2.email and user1.phoneNumber = user2.phoneNumber
}

fact automatedSOSMember {
	all user: User | user.age >= 6 implies user.sos = True -- 60 years is indicated with 6
}

fact automatedAssistance {
	all u: User | u.sos = True and u.healthStatus < 0 implies (one a : Assistance | a.user.ssn = u.ssn and a in AutomatedSOS.assistances)  iff 
		all ass: Assistance | ass in AutomatedSOS.assistances and ass.assistanceStatus = Finished implies ass.elapsedTime <= 5
}

fact samplingRequest {
	all s: Sampling | s.valid = True iff #s.users > 1000 and (all t: ThirdParty | s in t.sampling iff s.valid = True)
}
 

pred show {
	(some u: User | u.sos = True and #u.partyList > 3) and
	(some a: Assistance | a.assistanceStatus = Finished)
}

run show for 4

	


	
