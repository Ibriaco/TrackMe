open util/integer
open util/boolean

-- SIGNATURES

sig User {
	age: one Int,
	ssn: one Ssn,
	--email: one Email,
	--phoneNumber: one PhoneNumber,
	--address: one Address,
	data: one Data,
	sos: one Bool, -- 1 if the User is registered to AutomatedSOS, 0 otherwise
	--location: one Location,
	healthStatus: one Int, --if status is negative, the User is automatically assisted by ambulance
	partyList: set ThirdParty
}{
	age > 0
}

sig ThirdParty {
	ssn: one Ssn,
	accessibleUsers: set User,
	subbedTo: set User,
	samplings: set AnonymousSampling
}

sig Ssn {}
--sig Email {}
--sig PhoneNumber {}
--sig Address {}
sig Data {
	--weight: one Int,
	--height: one Int,
	--bloodGroup: one Int,
	--allergies: set Int
}

abstract sig Device{}
one sig Smartphone extends Device{}
one sig Smartwatch extends Device{}

/*sig Location {
	longitude: one Int,
	latitude: one Int
}
*/
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

sig IndividualAccessRequest {
	user: User,
	thirdParty: ThirdParty,
	found: one Bool,     -- True if a User has been found, False otherwise
	accepted: one Bool  -- True if the User accpets the ThirdParty's request, False otehrwise
}
	
sig AnonymousSampling {
	results: set User,
	valid: one Bool
}


-- FACTS

fact SSNAreUnique {
	(no disjoint user1, user2: User | user1.ssn = user2.ssn --or 
	--user1.email = user2.email or
	--user1.phoneNumber = user2.phoneNumber
	)
	and
	(no u: User, tp: ThirdParty | u.ssn = tp.ssn)
}


-- Third parties and requests
fact thirdPartySubscribedToUser {
	all u: User, tp: ThirdParty  | 
		u in tp.subbedTo implies u in tp.accessibleUsers and
		(u in tp.accessibleUsers implies tp in u.partyList) and 
		(tp in u.partyList implies u in tp.accessibleUsers)
}

fact userAccessibleFromThirdPartyOnlyIfRequestAccepted {
	all u: User, tp: ThirdParty | u in tp.accessibleUsers iff 
		(one r: IndividualAccessRequest | r.user.ssn = u.ssn and r.thirdParty.ssn = tp.ssn and r.accepted = True)
}

fact no2IndividualAccessRequests {
	no disjoint r1, r2: IndividualAccessRequest | r1.user = r2.user and r1.thirdParty = r2.thirdParty
}

fact noRequestsWithoutExistingThirdPArty {
	all r: IndividualAccessRequest | 
		(one tp: ThirdParty | r.thirdParty.ssn = tp.ssn)
}

fact requestAcceptedIffUserExists {
	all r: IndividualAccessRequest | 
		((r.found = False and r.accepted = False) or
		(r.found = True and r.accepted = False) or
		(r.found = True and r.accepted = True))
		and 
		(r.found = True iff (one u: User | u.ssn = r.user.ssn))
}

fact samplingRequestExistence {
	all s: AnonymousSampling | s in ThirdParty.samplings
}

fact samplingRequestValidity {
	all s: AnonymousSampling | 
		#s.results >= 1 implies s.valid = True --and -- here 1000 results to make a sampling valid is represented as 1
		--(all t: ThirdParty | s in t.samplings iff s.valid = True)
}


-- Automated SOS
fact automatedSOSMember {
	(all user: User | 
		(user in AutomatedSOS.monitoredPeople iff user.sos = True) and 
		(user.age >= 6 implies user.sos = True)) -- 60 years is indicated with 6
}

fact automatedAssistanceRequest {
	all u: User | (u.sos = True and u.healthStatus < 0) implies (one a : AssistanceRequest | a.user.ssn = u.ssn)
}

fact assistanceRequestSentWithin5Seconds {
	all a: AssistanceRequest | 
		(a.requestSent = False implies a.elapsedTime < 5) and  
		(a.elapsedTime >= 5 iff a.requestSent = True)
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

fact allAssistancesAreInAutomatedSOS {
	 all a: AssistanceRequest | a in AutomatedSOS.assistances
}


-- PREDICATES

pred createUser[u: User, s: Ssn, d: Data, st: Int] {
	u.ssn = s
	u.data = d
	--u.email = e
	--u.phoneNumber = p
	u.healthStatus = st
}

pred show[u: User] {
	#User > 1
	--u.healthStatus < 0
	--u.age = 7
}

run show
--run createUser for 2


	
