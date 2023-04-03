open extrema

sig A { R: set A }
sig S,T in A {}
one sig x in A {} -- for the "one-point" rules

fact { partial_order[A,R] }

run { some sup[A,R,A] }

check { -- (3.31)
	some sup[A,R,S]
	implies {
		
		above[A,R,S,sup[A,R,S]]

	}
}

check { -- (3.32)
	sup[A,R,x] = x
}

check {	-- (3.33)
	{ some sup[A,R,S]
		some sup[A,R,T]
	} implies {

			sup[A,R,S+T] = sup[A,R,sup[A,R,S] + sup[A,R,T]]

	}
}

check { -- (3.34)
	all y: A {

		above[A,R,none,y]

	}
}

check { -- (3.35)
	all x,y: A {
		some sup[A,R,x+y] implies {
			all z: A {

				(sup[A,R,x+y])-> z in R iff x->z in R and y->z in R

			}
		}
	}
}

check { -- (3.37)
	all x: A {

		sup[A,R,x+x] = x

	}
}

check {	-- (3.41)
	all y: A {
		
		bot[A,R] -> y in R

	}
}
