import mynat.definition -- imports the natural numbers {0,1,2,3,4,...}.
import mynat.add -- imports definition of addition on the natural numbers.
import mynat.mul -- imports definition of multiplication on the natural numbers.
namespace mynat -- hide


/- 
# Tutorial World

## Level 1: the `refl` tactic.

Let's learn some tactics. Let's start with the `refl` tactic. `refl` stands for "reflexivity", which is a fancy
way of saying that it will prove any goal of the form `A = A`. It doesn't matter how
complicated `A` is, all that matters is that the left hand side is *exactly equal* to the
right hand side (a computer scientist would say "definitionally equal"). I really mean
"press the same buttons on your computer in the same order" equal.
For example, `x * y + z = x * y + z` can be proved by `refl`, but `x + y = y + x` cannot.

Each level in this game involves proving a theorem or a lemma (a lemma is just a baby theorem).
The goal of the theorem will be a mathematical statement with a `⊢` just before it.
We will use tactics to manipulate and ultimately close (i.e. prove) these goals.

Let's see `refl` in action! At the bottom of the text in this box, there's a lemma,
which says that if $x$, $y$ and $z$ are natural numbers then $xy + z = xy + z$.
Locate this lemma (if you can't see the lemma and these instructions at the same time, make this box wider
by dragging the sides). Let's supply the proof. Click on the word `sorry` and then delete it.
When the system finishes being busy, you'll be able to see your goal -- the objective
of this level -- in the box on the top right. [NB if your system never finishes being busy, then
your computer is not running the javascript Lean which powers everything behind the scenes. 
Try Chrome? Try not using private browsing?] 

Remember that the goal is
the thing with the weird `⊢` thing just before it. The goal in this case is `x * y + z = x * y + z`,
where `x`, `y` and `z` are some of your very own natural numbers.
That's a pretty easy goal to prove -- you can just prove it with the `refl` tactic.
Where it used to say `sorry`, write

`refl,`

**and don't forget the comma**. Then hit enter to go onto the next line.
If all is well, Lean should tell you "Proof complete!" in the top right box, and there
should be no errors in the bottom right box. You just did the first
level of the tutorial! And you also learnt how to avoid by *far* the most
common mistake that beginner users make -- **every line must end with a comma**.
If things go weird and you don't understand why the top right box is empty,
check for missing commas. Also check you've spelt `refl` correctly: it's REFL
for "reflexivity".

For each level, the idea is to get Lean into this state: with the top right
box saying "Proof complete!" and the bottom right box empty (i.e. with no errors in).

If you want to be reminded about the `refl` tactic, you can click on the "Tactics" drop
down menu on the left. Resize the window if it's too small. 

Now click on "next level" in the top right of your browser to go onto the second level of
tutorial world, where we'll learn about the `rw` tactic.
-/

/- Lemma : no-side-bar
For all natural numbers $x$, $y$ and $z$, we have $xy + z = xy + z$.
-/
lemma example1 (x y z : mynat) : x * y + z = x * y + z :=
begin [nat_num_game]
  refl



end

/- Tactic : refl

## Summary

`refl` proves goals of the form `X = X`.

## Details

The `refl` tactic will close any goal of the form `A = B`
where `A` and `B` are *exactly the same thing*.

### Example:
If it looks like this in the top right hand box:
```
a b c d : mynat
⊢ (a + b) * (c + d) = (a + b) * (c + d)
```

then

`refl,`

will close the goal and solve the level. Don't forget the comma.

-/

end mynat -- hide 

