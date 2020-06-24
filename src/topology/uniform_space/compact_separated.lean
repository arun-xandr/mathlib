/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import topology.uniform_space.separation
/-!
# Compact separated uniform spaces

## Main statements

* `compact_space_uniformity`: On a separated compact uniform space, the topology determines the
  uniform structure, entourages are exactly the neighborhoods of the diagona.
* Heine-Cantor theorem: continuous functions on compact separated uniform spaces with values in
  uniform spaces are automatically uniformly continuous. There are several variations, the main one
  is `compact_space.uniform_continuous_of_continuous`.

## tags

uniform space, uniform continuity, compact space
-/

open_locale uniformity topological_space
open filter uniform_space set

variables {α β : Type*} [uniform_space α] [uniform_space β]

local notation `𝓟` := filter.principal

lemma compact_space_uniformity [compact_space α] [separated_space α] : 𝓤 α = ⨆ x : α, 𝓝 (x, x) :=
begin
  classical,
  suffices :  ∀ V ∈ ⨆ (x : α), 𝓝 (x, x), V ∈ 𝓤 α,
  { symmetry,
    exact le_antisymm nhds_le_uniformity this },
  by_contra H,
  push_neg at H,
  rcases H with ⟨V, V_in, h⟩,
  rw mem_supr_sets at V_in,
  let F := 𝓤 α ⊓ 𝓟 (-V),
  have : F ≠ ⊥,
  { rw inf_principal_ne_bot_iff ,
    intros U U_in,
    rw set.inter_compl_nonempty_iff,
    intro H,
    exact h (mem_sets_of_superset U_in H) },
  obtain ⟨⟨x, y⟩, hx⟩ : ∃ (x : α × α), F ⊓ 𝓝 x ≠ ⊥ := cluster_point_of_compact this,
  have : 𝓤 α ⊓ 𝓝 (x, y) ≠ ⊥,
  { apply ne_bot_of_le_ne_bot hx,
    apply inf_le_inf_right _ _,
    exact inf_le_left },
  have hxy : x = y := eq_of_uniformity_inf_nhds this,
  subst hxy,
  have : 𝓝 (x, x) ⊓ 𝓟 (-V) ≠ ⊥,
  { apply ne_bot_of_le_ne_bot hx,
    rw inf_comm,
    apply inf_le_inf_left _ _,
    exact inf_le_right },
  have : (x, x) ∉ interior V,
  { have : (x, x) ∈ closure (-V), by rwa closure_eq_nhds,
    rwa closure_compl at this },
  have : (x, x) ∈ interior V,
  { specialize V_in x,
    rwa mem_interior_iff_mem_nhds},
  contradiction
end


lemma unique_uniformity_of_compact_t2 {α : Type*} [t : topological_space α] [compact_space α]
[t2_space α] {u u' : uniform_space α}
(h : u.to_topological_space = t) (h' : u'.to_topological_space = t) : u = u' :=
begin
  apply uniform_space_eq,
  change uniformity _ = uniformity _,
  haveI : @compact_space α u.to_topological_space := by rw h ; assumption,
  haveI : @compact_space α u'.to_topological_space := by rw h' ; assumption,
  haveI : @separated_space α u := by rwa [separated_iff_t2, h],
  haveI : @separated_space α u' :=  by rwa [separated_iff_t2, h'],
  rw compact_space_uniformity,
  rw compact_space_uniformity,
  rw [h, h'],
end

/-- Heine-Cantor: a continuous function on a compact separated uniform space is uniformly continuous. -/
lemma compact_space.uniform_continuous_of_continuous [compact_space α] [separated_space α]
  {f : α → β} (h : continuous f) : uniform_continuous f :=
begin
  calc
  map (prod.map f f) (𝓤 α) = map (prod.map f f) (⨆ x, 𝓝 (x, x))  : by rw compact_space_uniformity
                       ... =  ⨆ x, map (prod.map f f) (𝓝 (x, x)) : by rw map_supr
                       ... ≤ ⨆ x, 𝓝 (f x, f x) : supr_le_supr (λ x, (h.prod_map h).continuous_at)
                       ... ≤ ⨆ y, 𝓝 (y, y)     : _
                       ... ≤ 𝓤 β               : nhds_le_uniformity ,
  rw ← supr_range,
  simp only [and_imp, supr_le_iff, prod.forall, supr_exists, mem_range, prod.mk.inj_iff],
  rintros _ _ ⟨y, rfl, rfl⟩,
  exact le_supr (λ x, 𝓝 (x, x)) (f y),
end

/-- Heine-Cantor: a continuous function on a compact separated set of a uniform space is
uniformly continuous. -/
lemma compact.uniform_continuous_on_of_continuous' {s : set α} {f : α → β}
  (hs : compact s) (hs' : is_separated s) (hf : continuous_on f s) : uniform_continuous_on f s :=
begin
  rw uniform_continuous_on_iff_restrict,
  rw is_separated_iff_induced at hs',
  rw compact_iff_compact_space at hs,
  rw continuous_on_iff_continuous_restrict at hf,
  resetI,
  exact compact_space.uniform_continuous_of_continuous hf,
end

/-- Heine-Cantor: a continuous function on a compact set of a separated uniform space
is uniformly continuous. -/
lemma compact.uniform_continuous_on_of_continuous [separated_space α] {s : set α} {f : α → β}
  (hs : compact s) (hf : continuous_on f s) : uniform_continuous_on f s :=
hs.uniform_continuous_on_of_continuous' (is_separated_of_separated_space s) hf
