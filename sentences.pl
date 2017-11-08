% David Ly, lydavid1, 1001435501

% TRIVIAL CASES
% student is not a complete noun phrase
test_sent([student,preferred,to,sleep], fails).
test_sent([the,student,sleep,the,teacher], fails).


% NP V_past inf_clause
test_sent([the,student,preferred,to,sleep]).
test_sent([the,student,expected,to,sleep]). % NP expected inf_clause (beginning with toinf)
test_sent([the,student,promised,to,sleep]). % apparently, we don't have to handle these?
test_sent([the,student,persuaded,to,sleep], fails). % 100% certain

% NP V_past NP inf_clause
test_sent([the,student,persuaded,the,teacher,to,sleep]).
test_sent([the,student,promised,the,teacher,to,sleep]).

% NP expected inf_clause (beginning with NP)
test_sent([the,student,expected,the,teacher,to,sleep]). % "the teacher to sleep" is a single constituent

test_sent([the,student,preferred,the,teacher,to,sleep], fails). % preferred cannot assign themes to 3 constituents, or its theme cannot be inf_clause that begins with NP


% NP V_past NP
test_sent([the,student,preferred,the,teacher]).
test_sent([the,student,persuaded,the,teacher]).
test_sent([the,student,promised,the,teacher]).
test_sent([the,student,expected,the,teacher], fails). % this actually sounds grammatical

test_sent([the,student,expected,the,teacher,persuaded,the,student,to,sleep]).
test_sent([the,student,preferred,the,teacher,persuaded,the,student,to,sleep], fails).
