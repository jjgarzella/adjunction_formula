import algebra.module.localized_module
import ring_theory.localization.at_prime
import linear_algebra.free_module.basic

universes u v

variables (R : Type u) [comm_ring R]
variables (M : Type v) [add_comm_group M] [module R M]

variables (P : ideal R) [hp : P.is_prime]


#check localized_module P.prime_compl M

variable (hm : module.free 
(localization.at_prime P) (localized_module P.prime_compl M))