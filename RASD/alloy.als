open util/integer
open util/boolean

---------------- SIGNATURES ----------------

-- The user signature: here are represented only the main attributes 
-- (SSN, age, health status and the list of third parties that can access to user's data)
sig User {
	ssn: one Ssn, 		     -- unique identifier
	age: one Int,
	sos: one Bool, 		     -- 1 if the User is registered to AutomatedSOS, 0 otherwise
	healthStatus: one Int,    -- if status is negative, the User is automatically assisted by ambulance
	partyList: set ThirdParty -- the list of third parties that can access to user's data
}{
	age > 0 			     -- user's age is a positive number	
}

sig ThirdParty {
	ssn: one Ssn,						-- unique identifier
	accessibleUsers: set User,				-- the list of the users accessible by the third party
	subbedTo: set User,					-- the of the users to which the third party is subscribed to
	samplings: set AnonymousSampling 	-- the list of sampling requested by the third party
}

sig Ssn {}		-- unique identifier for users and third parties

sig AssistanceRequest { 		-- AutomatedSOS assistance request
	user: one User,			-- the user for which the assistance request is formulated
	elapsedTime: one Int,	-- the amount of time passed between the moment in which the request 
						-- is formulated and the moment in which the request is sent to the ambulance system
	requestSent: one Bool	-- boolean indicating whether the request has already been sent to the ambulance system
} {
	elapsedTime >= 0 		-- the elapsed time is a positive integer
}

one sig AutomatedSOS {				-- the AutomatedSOS service entity
	monitoredPeople: set User,		-- the list of automatically assisted people
	assistances: set AssistanceRequest	-- the list of all formulated assistance requests
}

sig IndividualAccessRequest {  -- a request formulated by a third party to have access to a user's data
	user: User,			-- the user that a third party wants to have access to
	thirdParty: ThirdParty,	-- the third party requesting access for user's data
	found: one Bool,     		-- boolean indicating whether a user has been found or not
	accepted: one Bool  		-- boolean indicating whether the user has accepted the ThirdParty's request or not
}
	
sig AnonymousSampling {	-- an anonymous sampling request formulated by a third party according to some filters
	results: set User,		-- the list of users
	valid: one Bool			-- boolean indicating whether the samplig can be accomplished or not
}


---------------- FACTS ----------------

fact SSNAreUnique {
	-- all SSN are unique, both for users and third parties
	(no disjoint user1, user2: User | user1.ssn = user2.ssn) and
	(no u: User, tp: ThirdParty | u.ssn = tp.ssn)
}

fact thirdPartySubscribedToUser {
	all u: User, tp: ThirdParty  |
		-- a third party can subscribe to a user of and only if that user is accessible to the third party
		((u in tp.accessibleUsers) or (u in tp.accessibleUsers and u in tp.subbedTo)) and
	       -- if the user is accessible to a third party, than the user has that third party in his third parties list
		(u in tp.accessibleUsers iff tp in u.partyList)
}


fact userAccessibleFromThirdPartyOnlyIfRequestAccepted {
	-- a user is accessible to a third party if and only if exists a access request
	-- from that third party to that user that has been accepted
	all u: User, tp: ThirdParty | u in tp.accessibleUsers iff 
		(one r: IndividualAccessRequest | r.user.ssn = u.ssn and r.thirdParty.ssn = tp.ssn and r.accepted = True)
}

fact no2IndividualAccessRequests {
	-- for each pair (user;, third party) there's only one data access request
	no disjoint r1, r2: IndividualAccessRequest | r1.user = r2.user and r1.thirdParty = r2.thirdParty
}

fact noRequestsWithoutExistingThirdPArty {
	-- can't exist an access request from a non existing third party
	all r: IndividualAccessRequest | 
		(one tp: ThirdParty | r.thirdParty.ssn = tp.ssn)
}

fact requestAcceptedIffUserExists {
	-- can't exists an accepted access request if the involved user doesn't exist
	all r: IndividualAccessRequest | 
		((r.found = False and r.accepted = False) or
		(r.found = True and  r.accepted = False) or
		(r.found = True and r.accepted = True))
		and 
		(r.found = True iff (one u: User | u.ssn = r.user.ssn))
}

fact noSamplingWithoutThirdParty {
	all s: AnonymousSampling | s in ThirdParty.samplings
}

fact samplingRequestValidity {
	-- an anonymous sampling is valid (accepted by TrackMe if and only if 
	-- it involves more than 1000 users (1000 is represented by 1 in this model)
	all s: AnonymousSampling | 
		#s.results >= 1 implies s.valid = True
}


-- Automated SOS
fact automatedSOSMember {
	-- all people monitored by AutomatedSOS must be subscribed to it, hence the sos boolean must be set to True
	(all user: User | 
		(user in AutomatedSOS.monitoredPeople iff user.sos = True) and 
		-- if the user's age is greater or equal that 60 years (indicated in this model by value 6), 
		-- then he/she is automatically subscribed to AutomatedSOS
		(user.age >= 6 implies user.sos = True))
}

fact automatedAssistanceRequest {
	-- a user is automatically assisted if and only he/she is subscribed to AutomatedSOS 
	-- and his/her health status is negative (which means he/she is need of assistance)
	all u: User | (u.sos = True and u.healthStatus < 0) iff (one a : AssistanceRequest | a.user.ssn = u.ssn)
}

fact assistanceRequestSentWithin5Seconds {
	all a: AssistanceRequest | 
		-- if the request of assistance has not been sent, then the elapsed time can not be greter that 5 seconds
		(a.requestSent = False implies a.elapsedTime < 5) and  
		-- if the elapsed time is greater or equal to 5 seconds, then it means that a request has been sent
		(a.elapsedTime >= 5 iff a.requestSent = True)
}

fact noAssistanceForOKPeople {
	-- there is no assistance request sent for healthy people
	no a: AssistanceRequest | a.user.healthStatus >= 0
}

fact onlyOneAssistancePerUser {	
		-- there can be only one exclusive assistance for each user
		no disjoint a1, a2: AssistanceRequest | a1.user = a2.user
}

fact allAssistancesAreInAutomatedSOS {
	 all a: AssistanceRequest | a in AutomatedSOS.assistances
}

---------------- ASSERTIONS ----------------

assert uniquenessOfAssistanceRequestInAutomatedSOS {
	all u: User | 
		-- if a user's age is greater or equal than 60 and is subcribed to AutomatedSOS, then he/she is monitored by AutomatedSOS
		(u.age >= 6 and u.sos = True implies u in AutomatedSOS.monitoredPeople)  and
		-- a request is sent to a user if and only if his health status is negative and monitored by AutomatedSOS
		((one a: AssistanceRequest | a.user.ssn = u.ssn) iff (u.healthStatus < 0 and u in AutomatedSOS.monitoredPeople))
}

check uniquenessOfAssistanceRequestInAutomatedSOS

assert userAccessibleOnlyIfRequestAccepted {
	all u: User, tp: ThirdParty | 
		-- if a user is accessible by a third party, then there exists only one request sent by that third party and accepted by that user sent
		(u in tp.accessibleUsers implies (one r: IndividualAccessRequest | r.user = u and r.thirdParty = tp and r.accepted = True))
		and
		-- if a third party is subscribed to a user, then it implies also that that user is 
		-- accessible and there exists only one request sent by that third party and accepted by that user sent
		(u in tp.subbedTo implies (u in tp.accessibleUsers and 
			(one r: IndividualAccessRequest | r.user = u and r.thirdParty = tp and r.accepted = True)))
}
check userAccessibleOnlyIfRequestAccepted

assert noMoreThan5SecondsToSendAssistance {
	-- if the elapsed time is greater or equal that 5 seconds, then it means that a request has been sent
	all a: AssistanceRequest | a.elapsedTime >= 5 implies a.requestSent = True
}
check noMoreThan5SecondsToSendAssistance

---------------- PREDICATES ----------------

pred createUser[u: User, s: Ssn, st: Int] {
	u.ssn = s
	u.healthStatus = st
}

pred show[tp: ThirdParty] {
	#User > 1
	#AutomatedSOS.monitoredPeople > 0
	some u: User | u.healthStatus < 0
	some u: User | u in tp.accessibleUsers
	some r: IndividualAccessRequest | r.thirdParty.ssn = tp.ssn
}

run show



	
