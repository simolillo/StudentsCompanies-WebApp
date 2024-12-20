-- (lexicographic order)

// ----------------------------------------------
// SIGNATURES //
// ----------------------------------------------

sig Company extends User {
    intershipsOffered: disj set Internship
}

sig CV {}

sig Internship {}

sig Password {}

sig Student extends User {
    university: one University,
    cv: disj one CV,
    var status: one StudentStatus,
    var internship: lone Internship,
    var complaintPresence: one Boolean
}

sig University extends User {}

abstract sig User {
    username: disj one Username,
    password: disj one Password
}

sig Username {}


// ----------------------------------------------
// ENUMERATIONS //
// ----------------------------------------------

enum Boolean {
    True,
    False
}

enum StudentStatus {
    Searching,
    PreliminaryMatch,
    SelectionProcess,
    FinalMatch
}


// ----------------------------------------------
// FACTS //
// ----------------------------------------------

fact ifFinalMatchOnceSelectionProcess {
    all s: Student |
        always (
            s.status = FinalMatch implies
            once s.status = SelectionProcess    
        )
}

fact ifPreliminaryMatchOnceSearching {
    all s: Student |
        always (
            s.status = PreliminaryMatch implies
            once s.status = Searching    
        )
}

fact ifSearchingNoComplaint {
    all s: Student |
        always (
            s.status = Searching implies
            s.complaintPresence = False
        )
}

fact ifSelectionProcessOncePreliminaryMatch {
    all s: Student |
        always (
            s.status = SelectionProcess implies
            once s.status = PreliminaryMatch    
        )
}

fact internshipIffMatched {
    all s: Student |
        always (
            s.internship = none iff s.status = Searching
        )
}

fact noUnmappedCVs {#CV = #Student.cv}

fact noUnmappedInternships {all i: Internship | i in Company.intershipsOffered}

fact noUnmappedPasswords {#Password = #User.password}

fact noUnmappedUsernames {#Username = #User.username}

fact studentBehaviour {
    all s: Student |
        always(
            (one i: Internship | studentFindingMatch[s, i]) or
            studentStatusUpgrade[s] or
            studentEndingInternship[s] or
            companyComplains[s] or
            companyRemovesComplaint[s] or
            studentNotPassingSelectionProcess[s] or
            universityTerminatesInternship[s] or
            doNothing[s]
        )
}


// ----------------------------------------------
// PREDICATES //
// ----------------------------------------------

pred companyComplains [s: Student] {
    s.complaintPresence = False and
    s.complaintPresence' = True and
    statusUnchanged[s] and internshipUnchanged[s]
}

pred companyRemovesComplaint [s: Student] {
    s.complaintPresence = True and
    s.complaintPresence' = False
    statusUnchanged[s] and internshipUnchanged[s]
}

pred complaintPresenceUnchanged [s: Student] {
    s.complaintPresence' = s.complaintPresence
}

pred doNothing [s: Student] {
    statusUnchanged[s]
    internshipUnchanged[s]
    complaintPresenceUnchanged[s]
}

pred internshipUnchanged [s: Student] {
    s.internship' = s.internship
}

pred statusUnchanged [s: Student] {
    s.status' = s.status
}

pred studentEndingInternship [s: Student] {
    s.status = FinalMatch
    s.status' = Searching
    s.internship' = none
    s.complaintPresence' = False
}

pred studentFindingMatch [s: Student, i: Internship] {
    s.status = Searching
    s.status' = PreliminaryMatch
    s.internship' = i
    s.complaintPresence' = False
}

pred studentStatusUpgrade [s: Student] {
    (s.status = PreliminaryMatch and
    s.status' = SelectionProcess and
    internshipUnchanged[s] and complaintPresenceUnchanged[s]) or
    (s.status = SelectionProcess and
    s.status' = FinalMatch and
    internshipUnchanged[s] and complaintPresenceUnchanged[s])
}

pred studentNotPassingSelectionProcess [s: Student] {
    s.status = SelectionProcess
    s.status' = Searching
    s.internship' = none
    s.complaintPresence' = False
}

pred universityTerminatesInternship [s: Student] {
    s.status != Searching
    s.status' = Searching
    s.internship' = none
    s.complaintPresence' = False
}


// ----------------------------------------------
// RUN //
// ----------------------------------------------

// pred complaintTransition [s: Student] {
//     s.complaintPresence = False
//     s.complaintPresence''' = True
// }
// run complaintTransition for 10 but 4 steps

// pred studentProgression [s: Student] {
//     s.status = Searching
//     s.status' = PreliminaryMatch
//     s.status'' = SelectionProcess
//     s.complaintPresence''' = True
//     s.status'''' = FinalMatch
//     s.complaintPresence''''' = False
//     s.complaintPresence'''''' = True
//     s.status''''''' = Searching


//     #University = 1
//     #Internship = 1
//     #Company = 1
//     #Student = 1
// }
// run studentProgression for 10

// run {} for 3 steps