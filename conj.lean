-- import solutions to level 1
import complex.I

/-! 

# Level 2: Complex conjugation

-/

namespace complex

-- First complete the definition using `complex.mk` or `⟨x, y⟩` notation

/-- The complex conjugate of a complex number -/
def conj (z : ℂ) : ℂ := ⟨z.re,-z.im⟩  

-- Now prove how it interacts with everything else

/-! ## Real and imaginary parts -/

@[simp] lemma conj_re (z : ℂ) : re(conj z) = re(z) := begin refl end
@[simp] lemma conj_im (z : ℂ) : im(conj z) = -im(z) := begin refl end

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma conj_zero : conj 0 = 0 := 
begin 
    rw conj,
    ext,
    simp,
    simp,
end

@[simp] lemma conj_one : conj 1 = 1 := 
begin 
    rw conj,
    simp,
    refl,
end

@[simp] lemma conj_I : conj I = -I := 
begin
 /-     ext;
        simp, -/
    rw conj,
    simp,
    rw I,
    ext,
    simp,
    simp,
end

@[simp] lemma conj_neg_I : conj (-I) = I := 
begin
    rw conj,
    ext,
    simp,
    simp,
end

/-! # Behaviour with respect to +, - and * -/

@[simp] lemma conj_add (z w : ℂ) : conj (z + w) = conj z + conj w :=
begin
    rw conj,
    simp,
    ext,
    simp,
    simp,
    ring,
end

@[simp] lemma conj_neg (z : ℂ) : conj (-z) = -conj z := 
begin
    rw conj,
    simp,
    rw conj,
    ext,
    simp,
    simp,
end

@[simp] lemma conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w :=
begin
    repeat {rw conj},
    simp,
    ext,
    simp,
    simp,
    ring,

end

/-! # Properties of the `conj` map -/

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z :=
begin
    rw conj,
    rw conj,
    ext,
    simp,
    simp,
end

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w :=
begin
    rw conj,
    rw conj,
    simp,
    symmetry,
    rw ext_iff,
end

@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 :=
begin
    rw conj,
    rw ext_iff,
    simp,
    symmetry,
    rw ext_iff,
    simp,
end

/-- the ring homomorphism complex conjugation -/
def Conj : ℂ →+* ℂ :=
{ to_fun := conj,
  map_zero' := begin rw conj, ext, simp, simp, end,
  map_one' := begin rw conj, ext, simp, simp, end,
  map_add' := begin simp, end,
  map_mul' := begin simp, end
}

-- Two optional lemmas which computer scientists like,
-- giving us easy access to some basic properties
-- of conj

open function

lemma conj_involutive : involutive conj := 
begin
    apply conj_conj,
end

lemma conj_bijective : bijective conj := 
begin 
    unfold bijective,
    unfold injective,
    unfold surjective,
    split,
    intros,
    rw conj_inj at a,
    exact a,
    intro,
    have b.conj.conj,
    exact b,
    sorry
end

end complex
