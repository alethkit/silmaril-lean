---- MODULE MembershipForms ----
EXTENDS Naturals
VARIABLE x

Property == [][x \in {0, 1}]_x
Flag == [tag \in BOOLEAN |-> IF tag THEN 1 ELSE 0]
Applied == Flag[x \in {0, 1}]
Nested == [x \in {[tag \in BOOLEAN |-> tag][TRUE]}]_x
====
