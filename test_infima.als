open extrema

-- We'll need a set, A and a subset, S, thereof.  Crucially, we'll need
-- a relation R on A.  We can declare further subsets as and when we need them.
sig A { R: set A }
sig S in A {}


run { -- (3.1)
	partial_order[A,R]

	some y: A | below[A,R,S,y]
}

run { -- (3.2)
	partial_order[A,R]

	some x: A | infimum[A,R,S,x]
}

inf_S_below_S : check { -- (3.3)
	partial_order[A,R]
	implies {
		all x: A | infimum[A,R,S,x] implies below[A,R,S,x]
	}
}

inf_S_GLB : check { -- (3.4)
	partial_order[A,R]
	implies {
		all x: A | infimum[A,R,S,x] implies {
			all y: A | below[A,R,S,y] implies y->x in R
		}
	}
}

check { -- (3.5)
	partial_order[A,R]
  implies {
		all x: A | below[A,R,S,x] implies {
			all y: A | y->x in R implies below[A,R,S,y]
		}
	}
}

check { -- (3.6)
	partial_order[A,R]
	implies {
		  all x: A {
				{ below[A,R,S,x]
					all y: A | below[A,R,S,y] implies y->x in R
				} implies 
				infimum[A,R,S,x]
			}
	}
}

check {	-- (3.7)
	partial_order[A,R]
	implies {
		all x: A {

			infimum[A,R,S,x]
			iff
			{
				below[A,R,S,x]
				all y: A | below[A,R,S,y] implies y->x in R
			}

		}
	}
}

check { -- (3.8)
	partial_order[A,R]
	implies
	all u,v: A {

		u = v
		iff
		all y: A | y->u in R iff y->v in R

	}
}

atmost_one_inf: check {
	partial_order[A,R]
	implies
	all u,v: A {
		{	infimum[A,R,S,u]
			infimum[A,R,S,v]
		} implies u = v
	}
}

check {	-- (3.9)
	all x: A {

		S in x.R iff 	all s: S | x->s in R

	}
}

check { -- (3.10)
	{	partial_order[A,R]
		some inf[A,R,S] -- "Specifically, if inf.S exists..."
	} implies all y: A {

		S in y.R iff y->(inf[A,R,S]) in R

	}
}

-- A _complete lattice_ is a partially ordered set (A,R) in which inf.S exists
-- for all subsets S of A.  Throughout the rest of this section we assume that
-- we are dealing with a complete lattice.  The alternative is to tediously
-- preface every statement involving inf.S for some S with "assuming inf.S exists".
--
-- AWG: We can't quantify over subsets in Alloy and - although we could exploit
-- the completeness of finite lattices - we're not going to define lattices, yet.
-- So guess which of Roland's alternatives we going to use?

check { -- (3.11)
	{ partial_order[A,R]
		some inf[A,R,S]	-- "assuming inf.S exists" ;)
	} implies {

		below[A,R,S,inf[A,R,S]]

	}
}

-------------------------------------
-- Exploring the "is below" operator.
-------------------------------------

-- Create a singleton set {x} to play with (saves some quantification)
one sig x in A {}

check {	-- (3.12) the "one-point rule"
	partial_order[A,R]
	implies {

		all y: A | below[A,R,x,y] iff y->x in R

	}
}

-- Another set to play with
sig T in A {}

check {	-- (3.13) the "range disjunction rule"
	partial_order[A,R]
	implies
	all y: A {

		below[A,R,S+T,y] iff below[A,R,S,y] and below[A,R,T,y]

	}
}


check {	-- (3.14) the "empty range rule"
	partial_order[A,R]
	implies
	all y: A {

		below[A,R,none,y]

	}
}


-- Exploring the inf function, by analogy
check {	-- (3.15) the "one-point rule"
	{	partial_order[A,R]
		some inf[A,R,x]
	} implies {
		
		inf[A,R,x] = x

	}
}

check {	-- (3.16) the "range disjunction rule"
	{ partial_order[A,R]
		some inf[A,R,S]
		some inf[A,R,T]
		some inf[A,R,S+T]	-- Tedious? No! Helpfully explicit? Yes!
	} implies {

		inf[A,R,S+T] = inf[A,R,inf[A,R,S] + inf[A,R,T]]

	}
}

check {	-- (3.17) the "empty range rule"
	partial_order[A,R]
	implies
	all y: A {

		below[A,R,inf[A,R,none],y]

	}
}

check {	-- (3.19) Indirect equality
	{	partial_order[A,R]
		some inf[A,R,S]
	} implies {
		all z: A {

			z = inf[A,R,S]
			iff
			all y: A | y->z in R iff y->(inf[A,R,S]) in R

		}
	}
}

check { -- (3.20) Top
	partial_order[A,R]
	implies
	all y: A {

		y -> (top[A,R]) in R

	}
}
