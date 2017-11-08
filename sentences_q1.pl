% David Ly, lydavid1, 1001435501

% various acc NP
test_sent([she,fed,him]).
test_sent([she,fed,the,dog]).
test_sent([she,fed,dog], fails).
test_sent([she,fed,the,puppies]).
test_sent([she,fed,puppies]).

% NP V NP
test_sent([puppies,fed,him]).
test_sent([the,dog,with,puppies,fed,the,dog,with,puppies]).

% cannot interchange nom/acc case
test_sent([she,fed,she], fails).
test_sent([him,fed,she], fails).

% cannot attach pp to pronouns
test_sent([she,with,puppies,fed,him], fails).
test_sent([she,fed,him,with,puppies], fails).
