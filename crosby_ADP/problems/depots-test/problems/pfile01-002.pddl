(define (problem depotprob134536825) (:domain depots)
(:objects
	depot0 depot1 - Depot
	distributor0 distributor1 - Distributor
	truck0 - Truck
	pallet0 pallet1 pallet2 pallet3 - Pallet
	crate0 crate1 crate2 crate3 crate4 crate5 crate6 crate7 crate8 crate9 crate10 crate11 crate12 crate13 crate14 crate15 crate16 crate17 crate18 crate19 crate20 crate21 crate22 crate23 crate24 - Crate
	hoist0 hoist1 hoist2 hoist3 - Hoist)
(:init
	(at pallet0 depot0)
	(clear crate23)
	(at pallet1 depot1)
	(clear crate24)
	(at pallet2 distributor0)
	(clear crate21)
	(at pallet3 distributor1)
	(clear crate17)
	(at truck0 depot0)
	(at hoist0 depot0)
	(available hoist0)
	(at hoist1 depot1)
	(available hoist1)
	(at hoist2 distributor0)
	(available hoist2)
	(at hoist3 distributor1)
	(available hoist3)
	(at crate0 depot0)
	(on crate0 pallet0)
	(at crate1 depot0)
	(on crate1 crate0)
	(at crate2 distributor1)
	(on crate2 pallet3)
	(at crate3 distributor0)
	(on crate3 pallet2)
	(at crate4 distributor0)
	(on crate4 crate3)
	(at crate5 depot0)
	(on crate5 crate1)
	(at crate6 depot1)
	(on crate6 pallet1)
	(at crate7 depot0)
	(on crate7 crate5)
	(at crate8 depot1)
	(on crate8 crate6)
	(at crate9 distributor0)
	(on crate9 crate4)
	(at crate10 depot1)
	(on crate10 crate8)
	(at crate11 depot1)
	(on crate11 crate10)
	(at crate12 distributor1)
	(on crate12 crate2)
	(at crate13 distributor0)
	(on crate13 crate9)
	(at crate14 distributor0)
	(on crate14 crate13)
	(at crate15 distributor0)
	(on crate15 crate14)
	(at crate16 depot1)
	(on crate16 crate11)
	(at crate17 distributor1)
	(on crate17 crate12)
	(at crate18 depot1)
	(on crate18 crate16)
	(at crate19 depot0)
	(on crate19 crate7)
	(at crate20 depot1)
	(on crate20 crate18)
	(at crate21 distributor0)
	(on crate21 crate15)
	(at crate22 depot0)
	(on crate22 crate19)
	(at crate23 depot0)
	(on crate23 crate22)
	(at crate24 depot1)
	(on crate24 crate20)
)

(:goal (and
		(on crate1 crate5)
		(on crate2 crate18)
		(on crate3 pallet0)
		(on crate4 crate3)
		(on crate5 crate14)
		(on crate6 crate11)
		(on crate8 crate17)
		(on crate9 crate24)
		(on crate10 crate16)
		(on crate11 crate8)
		(on crate12 crate2)
		(on crate13 crate4)
		(on crate14 crate10)
		(on crate15 crate19)
		(on crate16 crate9)
		(on crate17 pallet1)
		(on crate18 crate22)
		(on crate19 pallet3)
		(on crate22 crate13)
		(on crate23 pallet2)
		(on crate24 crate23)
	)
))
