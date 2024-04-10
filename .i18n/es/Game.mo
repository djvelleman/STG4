��            )   �      �     �     �     �     �  8   �  8   6  Q   o  Q   �  �     �   �  �   [  �   "  �   �  #   �  (   �  t   �  �  M    
  �     _   �  r  I  g  �  D   $  �   i  B     #   N  	   r     |  "   �    �  )   �     �     �  #     9   <  9   v  R   �  R     \   V  b   �       y   �  �     9   �  &   �  c     �   k  �  4  �     g   �  5    .  H  O   w  �   �  P   t   8   �   	   �      !  #   !                                                                          
                                                     	          A tricky subset proof Combination World Complement of a union Complement of an intersection For any sets $A$ and $B$, $(A \cap B)^c = A^c \cup B^c$. For any sets $A$ and $B$, $(A \cup B)^c = A^c \cap B^c$. For any sets $A$, $B$, and $C$, $A \cap (B \cup C) = (A \cap B) \cup (A \cap C)$. For any sets $A$, $B$, and $C$, $A \cup (B \cap C) = (A \cup B) \cap (A \cup C)$. For any sets `A` and `B`, `compl_inter A B` is a proof of the
statement `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`.  In Mathlib, the name of this theorem is `Set.compl_inter`. For any sets `A` and `B`, `compl_union A B` is a proof of the
statement `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`.  In Mathlib, the name of this theorem is `Set.compl_union`. For any sets `A`, `B`, and `C`, `inter_distrib_left A B C` is a proof of the
statement `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.  In Mathlib, the name of this theorem
is `Set.inter_distrib_left`. For any sets `A`, `B`, and `C`, `union_distrib_left A B C` is a proof of the
statement `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`.  In Mathlib, the name of this theorem
is `Set.union_distrib_left`. In this world you'll prove theorems combining complements, intersections, and unions.  For
the most part, we'll leave you on your own to figure out these proofs. Intersection distributes over union Notice that you haven't used `h2` yet... Now that you know `«{x}» ∈ B ∪ C`, you can use that
statement as the basis for breaking your proof into cases. Now use `have` to assert that `«{x}» ∈ A ∪ C`.  If you don't see right
away how to justify this assertion, you can just write `have hAC : «{x}» ∈ A ∪ C` and Lean will
set `«{x}» ∈ A ∪ C` as your immediate goal.  Once you achieve that goal, Lean will add
`hAC : «{x}» ∈ A ∪ C` to your list of assumptions, and you can continue with
the proof of your original goal.  For further details, click on `have` in the list of tactics
on the right. Of course, you could start the proof in this level with either `ext x` or `apply Subset.antisymm`.
But there is a shorter solution: you can use
the theorem from the previous level (`compl_union`) to prove the
theorem in this level.

The trick to get started on this proof is to rewrite `Aᶜ ∪ Bᶜ` as `(Aᶜ ∪ Bᶜ)ᶜᶜ`.  As you
know, `compl_compl (Aᶜ ∪ Bᶜ)` is a proof of the theorem `(Aᶜ ∪ Bᶜ)ᶜᶜ = Aᶜ ∪ Bᶜ`, and therefore
`rewrite [compl_compl (Aᶜ ∪ Bᶜ)]` could be used to rewrite `(Aᶜ ∪ Bᶜ)ᶜᶜ` as `Aᶜ ∪ Bᶜ`; but we
want to go in the opposite direction, rewriting `Aᶜ ∪ Bᶜ` as `(Aᶜ ∪ Bᶜ)ᶜᶜ`. To do that, use
`rewrite [← compl_compl (Aᶜ ∪ Bᶜ)]`. (To enter the left-pointing arrow, type `\l`.) Once again, Lean has left out some parentheses that it regards as unnecessary.
Lean gives intersection higher precedence than union, so it interprets
`A ∩ B ∪ A ∩ C` as `(A ∩ B) ∪ (A ∩ C)`. Suppose $A \cup C \subseteq B \cup C$ and $A \cap C \subseteq B \cap C$.  Then $A \subseteq B$. There is more than one way to do the proof in this level.  Since the proof involves complements of
sets, negative statements will arise in the course of the proof.  This suggests two possible techniques.
You may be able to use the `push_neg` tactic to reexpress some negative statements as equivalent
positive statements.  And you may find proof by contradiction useful. This is different from the previous theorem--the roles of union and intersection have
been swapped.

Once again, there is a tricky shortcut: there is a way to use the theorem from the
previous level to prove this theorem.

But if you don't see the shortcut, you can use a straightforward approach.
If you made it through the last one, you can do this one too! This proof is a bit tricky.  But you should know how to get started. This proof is longer than previous ones, but it doesn't require any new tactics or theorems.
Just stick with it and keep applying the ideas from previous levels! To finish off Combination World, we'll do one more tricky theorem. Union distributes over intersection Use `h1`. Whew! You've finished Combination World! Project-Id-Version: Game v4.7.0
Report-Msgid-Bugs-To: 
PO-Revision-Date: 
Last-Translator: 
Language-Team: none
Language: es
MIME-Version: 1.0
Content-Type: text/plain; charset=UTF-8
Content-Transfer-Encoding: 8bit
Plural-Forms: nplurals=2; plural=(n != 1);
X-Generator: Poedit 3.0.1
 Una demostración de contenido complidada Mundo combinado Complementario de la unión Complementario de una intersección Dados conjuntos $A$ y $B$, $(A \cap B)^c = A^c \cup B^c$. Dados conjuntos $A$ y $B$, $(A \cup B)^c = A^c \cap B^c$. Dados conjuntos $A$, $B$, y $C$, $A \cap (B \cup C) = (A \cap B) \cup (A \cap C)$. Dados conjuntos $A$, $B$, y $C$, $A \cup (B \cap C) = (A \cup B) \cap (A \cup C)$. Dados conjuntos `A` y `B`, `comp_inter A B` es una prueba de `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`. Dados conjuntos `A` and `B`, `comp_union A B` es una prueba de que `(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ`. Dados conjuntos `A`, `B`, y `C`, `inter_distrib_over_union A B C` es una prueba de
`A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`. Dados conjuntos `A`, `B`, y `C`, `union_distrib_left A B C` es una prueba de
`A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`. En este mundo, probarás teoremas que involucran complementarios, intersecciones y uniones.
La mayor parte del tiempo tendrás que hacerlo sin ayuda. Distributividad de la intersección respecto de la unión Fíjate en que aún no has usado `h2`. Ahora sabes que `x ∈ B ∪ C`, puedes usar eso como base
  para partir la demostración en casos. Ahora usa `have` para establecer que `{x} ∈ A ∪ C`. Recuerda que, tal
  como vimos en la descripción de la táctica `have`, esto se puede hacer aunque no veas cómo
  demostrarla en un solo paso. Como de costrumbre, podrías empezar esta prueba con `ext x` o `apply sub_antisymm`.
Pero hay una solución más corta: puedes usar el teorema del nivel anterior (`comp_union`) para
probar el teorema de este nivel.

El truco para empezar es reescribir `Aᶜ ∪ Bᶜ` como `(Aᶜ ∪ Bᶜ)ᶜᶜ`. Como sabes, `comp_comp (Aᶜ ∪ Bᶜ)`
es una prueba de `(Aᶜ ∪ Bᶜ)ᶜᶜ = Aᶜ ∪ Bᶜ`, así que se podría usar`rewrite [comp_comp (Aᶜ ∪ Bᶜ)]`
para reescribir `(Aᶜ ∪ Bᶜ)ᶜᶜ` como `Aᶜ ∪ Bᶜ`; pero queremos ir en la otra dirección, reescribiendo
`Aᶜ ∪ Bᶜ` como `(Aᶜ ∪ Bᶜ)ᶜᶜ`. Para ello, usa `rewrite [← comp_comp (Aᶜ ∪ Bᶜ)]`.
(Para introducir la flecha hacia la izquierda, teclea `\\l`.) Puede ser útil separar la segunda parte de `{h}` como una
  hiótesis separada. Lo puedes hacer con `have {h}BC : {x} ∈ B ∪ C := {h}.right`. Supongamos que $A \cup C \subseteq B \cup C$ y $A \cap C \subseteq B \cap C$. Entonces $A \subseteq B$. Conforme las pruebas se van volviendo más difíciles, puedes descubrir que es útil usar la
táctica `have` para establecer una afirmación cuya demostración es demasíado compleja para hacerla
en una línea.
Para ver ayuda sobre cómo hacerlo, puedes pulsar en `have` en la lista de tácticas a la derecha. Este es diferente del anterior: el papel de la unión e intersección se ha intercambiado.

De nuevo, se puede usar un atajo: hay una forma de usar el teorema anterior para demostrar este
teorema.

Pero si no ves el atajo, puedes usar el método directo. ¡Si pudiste con el anterior, podrás con
este! Esta prueba es un poco complicada. Pero deberías saber al menos cómo empezar. Esta prueba es más larga que las anteriores, pero no requiere nuevas tácticas o teoremas.
Símplemente tienes que ir trabajándola, usando tácticas y teoremas ya vistos. Para terminar el mundo de las uniones, veremos un último teorema complicadillo. Distributividad de la unión respecto a la intersección Usa `h1`. ¡Lo conseguiste! ¡Has terminado el mundo combinado! 