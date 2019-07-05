import ring_theory.principal_ideal_domain linear_algebra.basis
open submodule dfinsupp
universes u v


variables (R : Type u) (M : Type u) [principal_ideal_domain R] [has_zero (Type u)]
          (ι : Type u) [decidable_eq ι] [Π i : ι, decidable_pred (eq 0)]
          [add_comm_group M] [module R M] (A : submodule R M)


lemma exists_rep (x : submodule.quotient A) : 
∃ a : M, submodule.quotient.mk a = x := @quotient.exists_rep M (quotient_rel A) x 

section scratch

variables {R} {M} (supp : finset ι) (ideal_fun : ι → ideal R) (Hfg : fg A)
/- working out some stuff
variable proj : Π i : (↑supp: set ι), (submodule.quotient∘ideal_fun) i.1
def quot_ring_sum : direct_sum ι (submodule.quotient∘ideal_fun) :=
direct_sum.mk (submodule.quotient∘ideal_fun) supp proj 
-/

instance acg (i : ι) : add_comm_group (quotient $ ideal_fun i) := by apply_instance

def decomp (f : ι → ideal R) (hf : sorry) : linear_equiv R A (direct_sum ι (submodule.quotient∘f)) :=
sorry

theorem exists_ideals : ∃ f : ι → ideal R, sorry := sorry

theorem unique_of_decomp (f g : ι → ideal R) 
(equivf : linear_equiv R A $ direct_sum ι (submodule.quotient∘f))
(equivg : linear_equiv R A $ direct_sum ι (submodule.quotient∘g)) : f = g := sorry

end scratch

namespace torsion

variables (a : A) {M} (R A)

@[reducible] def ord_ideal : ideal R := 
⟨   {r : R | r • a = 0}, 
    zero_smul R a, 
    λ x y hx hy, by rw set.mem_set_of_eq at hx hy ⊢; 
                rw [add_smul x y a, hx, hy, zero_add],
    λ c x h, by rw set.mem_set_of_eq at h ⊢; 
                rw [smul_eq_mul, ←smul_smul R c x, h, smul_zero c]⟩

lemma ord_ideal_zero_eq_univ : (ord_ideal R A 0).1 = set.univ :=
set.ext (λ x, iff.intro (λ h, set.mem_univ x) (λ h, by apply smul_zero))


def torsion_submodule : submodule R ↥A :=
⟨   {a₁ : A | ∃ r : R, r ≠ 0 ∧ r ∈ (ord_ideal R A a₁).1},
    ⟨1, ⟨ne.symm $ integral_domain.zero_ne_one R, smul_zero 1⟩⟩,
    λ x y hx hy, by rcases hx with ⟨r, ⟨hr0, hr⟩⟩; rcases hy with ⟨s, ⟨hs0, hs⟩⟩;
                           use (r*s); 
                           rw set.mem_set_of_eq at hs hr ⊢;
                           exact ⟨λ h, absurd (zero_eq_mul.1 h.symm) $ not_or hr0 hs0,
                                  by rw [smul_add (r*s) x y, ←smul_smul R r s y, 
                                  hs, mul_comm, ←smul_smul R s r]; norm_num [hr]⟩,
    λ c x h, by rcases h with ⟨r, ⟨hr0, hr⟩⟩; 
                use r; 
                rw set.mem_set_of_eq at hr ⊢;
                exact ⟨hr0, by rw [smul_smul R r c, mul_comm, ←smul_smul R c r, hr, smul_zero]⟩⟩

@[reducible] def submodule_self : submodule R ↥A :=
by refine {carrier := set.univ, ..}; intros; apply set.mem_univ


section 
variables (M)
@[reducible] def submodule_univ : submodule R M :=
by refine {carrier := set.univ, ..}; intros; apply set.mem_univ
end

/-can't remember what these were for but maybe they'll be useful
lemma univ_coe_eq_self : submodule_univ R ↥A = submodule_self R A := rfl
def submodule_inter (B : submodule R M) : submodule R M :=
⟨   A.1 ∩ B.1, ⟨A.2, B.2⟩, 
    λ x y hx hy, ⟨A.3 hx.1 hy.1, B.3 hx.2 hy.2⟩, 
    λ c x hx, ⟨A.4 c hx.1, B.4 c hx.2⟩⟩
-/
def submodule_embed (B : submodule R ↥A) : submodule R M :=
⟨   A.subtype '' B.1, ⟨0, ⟨B.2, linear_map.map_zero A.subtype⟩⟩, 
    λ x y hx hy, by rcases hx with ⟨x', ⟨hxi, hx⟩⟩; rcases hy with ⟨y', ⟨hyi, hy⟩⟩;
        exact ⟨x' + y', B.3 hxi hyi, by rw [hx.symm,hy.symm]; exact A.subtype.2 x' y'⟩, 
    λ c x hx, by {rcases hx with ⟨x', ⟨hxi, hx⟩⟩, simp,
        exact ⟨c•x', ⟨B.4 c hxi, by rw [hx.symm, coe_smul, subtype_apply]⟩⟩}⟩

lemma torsion_of_torsion_submodule : submodule_self R (torsion_submodule R A) = (torsion_submodule R (torsion_submodule R A)) :=
ext $ λ x, iff.intro 
    (λ h, by rcases x.2 with ⟨r, ⟨hz, hr⟩⟩; exact ⟨r, ⟨hz, subtype.eq' hr⟩⟩) $
     λ h, by simp [submodule_self, x.2]

def torsion_decomp_fun : bool → Type u := 
λ b, ite (b = tt) ((torsion_submodule R A) : Type u) (submodule.quotient (torsion_submodule R A))

@[simp] lemma torsion_decomp_fun_tt : torsion_decomp_fun R A tt = torsion_submodule R A := rfl
@[simp] lemma torsion_decomp_fun_ff : torsion_decomp_fun R A ff = submodule.quotient (torsion_submodule R A) := rfl

instance acg_torsion_decomp_fun : Π b : bool, add_comm_group (torsion_decomp_fun R A b) := 
by rintro ⟨ff, tt⟩; simp; apply_instance

instance module_torsion_decomp_fun : Π b : bool, module R (torsion_decomp_fun R A b) :=
by {  rintro ⟨ff, tt⟩,
      show (module R (submodule.quotient _)), by apply_instance,
      show (module R (torsion_submodule R A)), by apply_instance}
--strange..

@[reducible] def torsion_decomp := direct_sum bool (torsion_decomp_fun R A)

instance acg_decomp : add_comm_group (torsion_decomp R A) := by apply_instance

instance module_decomp : module R (torsion_decomp R A) := by apply_instance


@[reducible] def torsion_free := torsion_submodule R A = 0

end torsion 

namespace free
variables (α : Type u) (β : Type u) [ring α] [add_comm_group β] 
          [module α β]


-- def has_nonemp_basis := ∃ s : set M, ¬s = ∅ ∧ is_basis R s

--def free_fin_rk' (n : ℕ) := direct_sum (fin n) (λ i, α)
--def free_fin_rk := direct_sum l (λ i, α)
--instance module_free : module α free_fin_rk := by sorry


--not really sure how I'm going to do free modules yet
--on the free module thread on Zulip Kenny suggests using direct_sum or finsupp
--Mario says lc is dumb and finsupp should be used... I'm going to look at linear_combination.lean
--more closely and just write some equivalent definitions and see what goes wrong and work
--out what to do from there. 

--With this definition I don't have to decide any of the above yet..
structure free_on :=
(basis : set β)
(nonempty : ¬basis = ∅)
(free : ∃ (i : basis → β), ∀ (γ : Type u) [add_comm_group γ] [module α γ] (f : basis → γ), 
        ∃! φ : linear_map α β γ, φ∘i = f)

-- but not sure I want it to be a structure and it did weird things as a class. 
-- I want to use a definition but I get a red underline under "module" because
-- apparently [add_comm_group γ] can't be synthesised.

/-def free := ∃ basis : set β, ¬basis = ∅ ∧ 
        (∃ (i : basis → β), ∀ (γ : Type u) [add_comm_group γ] [module α γ] (f : basis → γ), 
        ∃! φ : linear_map α β γ, φ∘i = f) -/

/-
lemma free_of_free_on (H : free_on α β) : 
∃ s : set β, (¬s = ∅ ∧ is_basis α s) :=
⟨H.1, ⟨H.2, by
{cases H.3, 
split,
sorry, sorry,
}
⟩⟩ 
end free
-/ 
open torsion free

namespace pid

theorem free_of_submodule_of_free (H : free_on R M) (G : submodule R M) :
∃ s : set G, (¬s = ∅ ∧ is_basis R s) := sorry
--fails to synthesise [has_zero (Type ?)]

theorem free_of_fg_torsion_free (Hfg : fg A) (H : torsion_free R A): 
∃ s : set A, (¬s = ∅ ∧ is_basis R s) := sorry

local notation `At` := torsion_submodule R A


lemma torsion_free_of_torsion_quotient : 
torsion_free R (submodule_univ R (submodule.quotient At)) :=
by apply submodule.ext;
exact 
(λ x, iff.intro 
(λ h, by {rw [zero_eq_bot, mem_bot], rcases h with ⟨r, ⟨hr0, hr⟩⟩,
 cases (exists_rep R A At x.1) with a ha, 
 have h : r•a ∈ At, by apply (quotient.mk_eq_zero At).1;
                            rw [quotient.mk_smul, ha]; sorry,
        rcases h with ⟨s, ⟨hs0, hs⟩⟩, 
        rw [subtype.ext, ha.symm],
        apply (quotient.mk_eq_zero At).2,
        exact ⟨s*r, ⟨λ h, absurd (zero_eq_mul.1 h.symm) $ not_or hs0 hr0,
                        by rwa [set.mem_set_of_eq, ←smul_smul]⟩⟩}) 
(λ h, by {rw [zero_eq_bot, mem_bot] at h, rw h, 
          exact ⟨1, ⟨ne.symm $ integral_domain.zero_ne_one R,
                     by rw ord_ideal_zero_eq_univ R _; exact set.mem_univ 1⟩⟩}))


def equiv_sum_torsion_torsion_quotient : A ≃ₗ[R] torsion_decomp R A := 
{to_fun := sorry,
add := sorry,
smul := sorry,
inv_fun := sorry,
left_inv := sorry,
right_inv := sorry}


end pid

end free