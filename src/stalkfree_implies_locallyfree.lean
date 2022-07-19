
--import algebra.module.
import ring_theory.algebra_tower
import ring_theory.localization.away
import ring_theory.localization.at_prime
import linear_algebra.free_module.basic

universes u v

variables (R : Type u) [comm_ring R]
variables (M : Type v) [add_comm_group M] [module R M]

variables (P : ideal R) [hp : P.is_prime]

#check localization.at_prime P
variable f : R
#check localization.away f

variables (R' : Type u) [is_localization.at_prime R P]
--variables (M' : Type v) [is_localization.at_prime M P]

--lemma away_free_of_free_at_prime


-- lemma away_free_of_free_at_prime 
-- (hm : module.free (localization.at_prime P) 
-- (localization.at_prime P M)) : 
-- (∃ f : R, (module.free (localization.away f R)
-- (localization.away f M))) := sorry