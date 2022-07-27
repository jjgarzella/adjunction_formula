import algebra.module.localized_module
--import ring_theory.algebra_tower
--import ring_theory.localization.away
import ring_theory.localization.at_prime
import linear_algebra.free_module.basic

universes u v

variables (R : Type u) [comm_ring R]
variables (M : Type v) [add_comm_group M] [module R M]

variables (P : ideal R) [hp : P.is_prime]
include hp

--TODO: write a version of localization.away and
--      localization.at_prime for localizations of modules


lemma away_free_of_free_at_prime 
(hm : module.free (localization.at_prime P)
(localized_module P.prime_compl M)) : 
(∃ f : R, (module.free (localization.away f)
(localized_module (submonoid.powers f) M)))
:= sorry
