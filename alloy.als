open util/integer
open util/boolean

-- SIGNATURES

sig User {
	age: one Int,
	ssn: one String,
	email: one String,
	phoneNumber: one String,
	sos: one Bool, -- 1 if the User is registered to AutomatedSOS, 0 otherwise
	location: one Location,
	healthStatus: one Int, --if status is negative, the User is automatically assisted by ambulance
	partyList: set ThirdParty
}{
	age > 0
}

sig ThirdParty {
	name: one String,
	ssn: one String,
	accessibleUser: set User,
	subbedTo: set User,
	sampling: set AnonymousSampling
}

abstract sig Device{}
one sig Smartphone extends Device{}
one sig Smartwatch extends Device{}

sig Location {
	longitude: one Int,
	latitude: one Int
}

/*
abstract sig AssistanceStatus{}
one sig Started extends AssistanceStatus{}
one sig Finished extends AssistanceStatus{}
*/

sig AssistanceRequest {
	user: one User,
	elapsedTime: one Int,
	requestSent: one Bool
} {
	elapsedTime >= 0
}

one sig AutomatedSOS {
	monitoredPeople: set User,
	assistances: set AssistanceRequest
}

sig IndividualRequest {
	ssn: String,
	thirdPartySsn: String,
	found: one Bool,     -- True if a User has been found, False otherwise
	accepted: one Bool  -- True if the User accpets the ThirdParty's request, False otehrwise
}
	
sig AnonymousSampling {
	result: set User,
	valid: one Bool
}


-- FACTS

fact SSNAreUnique {
	(no disjoint user1, user2: User | user1.ssn = user2.ssn or 
	user1.email = user2.email or
	user1.phoneNumber = user2.phoneNumber)
	and
	(no u: User, tp: ThirdParty | u.ssn = tp.ssn)
}


-- Third parties and requests
fact thirdPartySubscribedToUser {
	all u: User, tp: ThirdParty  | 
		u in tp.subbedTo implies u in tp.accessibleUser and tp in u.partyList iff u in tp.accessibleUser
}

fact userAccessibleFromThirdPartyOnlyIfRequestAccepted {
	all u: User, tp: ThirdParty | u in tp.accessibleUser iff 
		(all r: IndividualRequest | r.ssn = u.ssn and r.thirdPartySsn = tp.ssn and r.accepted = True)
}

fact noRequestsWithoutExistingThirdPArty {
	no r: IndividualRequest | 
		(no tp: ThirdParty | r.thirdPartySsn = tp.ssn)
}

fact requestAcceptedIffUserExists {
	all r: IndividualRequest | 
		((r.found = False and r.accepted = False) or
		(r.found = True and r.accepted = False) or
		(r.found = True and r.accepted = True))
		and 
		(r.found = True iff (one u: User | u.ssn = r.ssn))
}

fact samplingRequest {
	all s: AnonymousSampling | #s.result >= 1 implies s.valid = True and -- here 1000 results to make a sampling valid is represented as 1
		(all t: ThirdParty | s in t.sampling iff s.valid = True)
}


-- Automated SOS
fact automatedSOSMember {
	(all user: User | 
		(user in AutomatedSOS.monitoredPeople iff user.sos = True) and 
		(user.age >= 6 implies user.sos = True)) -- 60 years is indicated with 6
}

fact automatedAssistance {
	all u: User | (u.sos = True and u.healthStatus < 0)
		implies (one a : AssistanceRequest | a.user.ssn = u.ssn and 
			((a.requestSent = False implies a.elapsedTime < 5) and  (a.elapsedTime >= 5 implies a.requestSent = True)))
}

fact noAssistanceForOKPeople {
	no a: AssistanceRequest | a.user.healthStatus >= 0
}

fact onlyOneAssistancePerUser {
		no disjoint a1, a2: AssistanceRequest | a1.user = a2.user
	/*	a1.user.ssn = a2.user.ssn and
		a1.user.email = a2.user.email and 
		a1.user.phoneNumber = a2.user.phoneNumber */
}

fact allAssistancesAreInAutomatedSOS{
	 all a: AssistanceRequest | a in AutomatedSOS.assistances
}


-- PREDICATES

pred createUser[u: User, s: String, e: String, p: String, st: Int] {
	u.ssn = s
	u.email = e
	u.phoneNumber = p
	u.healthStatus = st
}

pred show[u: User, u2: User, tp: ThirdParty] {
	#User > 1
	u.healthStatus < 0
	u.age = 7
	u.ssn = "ssn" and u.email = "email" and u.phoneNumber = "number"
	u2.ssn = "ssn_2" and u2.email = "email_2" and u2.phoneNumber = "number_2"
	tp.ssn = "tp_ssn"
}

run show
run createUser for 2


	
