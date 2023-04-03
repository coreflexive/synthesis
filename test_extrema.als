open extrema

sig A { R: set A }
sig S in A {}

fact { partial_order[A,R] }

check {
	some inf[A,R,above[A,R,S]]
	implies {

		some sup[A,R,S]

	}
}

check { -- Ex.3.46
	some sup[A,R,S]
	implies {

		some inf[A,R,above[A,R,S]]

	}
}


check { -- (3.42)
	some inf[A,R,above[A,R,S]]
	implies {

		sup[A,R,S] = inf[A,R,above[A,R,S]]

	}
}

check { -- dual(3.42)
	some sup[A,R,below[A,R,S]]
	implies {

		inf[A,R,S] = sup[A,R,below[A,R,S]]

	}
}
