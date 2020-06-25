(define (problem depotprob134536825) (:domain depots)
(:objects
	depot0 depot1 depot2 - Depot
	distributor0 distributor1 distributor2 - Distributor
	truck0 truck1 - Truck
	pallet0 pallet1 pallet2 pallet3 pallet4 pallet5 - Pallet
	crate0 crate1 crate2 crate3 crate4 crate5 crate6 crate7 crate8 crate9 crate10 crate11 crate12 crate13 crate14 crate15 crate16 crate17 crate18 crate19 crate20 crate21 crate22 crate23 crate24 crate25 crate26 crate27 crate28 crate29 - Crate
	hoist0 hoist1 hoist2 hoist3 hoist4 hoist5 - Hoist)
(:init
	(at pallet0 depot0)
	(clear crate28)
	(at pallet1 depot1)
	(clear crate29)
	(at pallet2 depot2)
	(clear crate26)
	(at pallet3 distributor0)
	(clear crate11)
	(at pallet4 distributor1)
	(clear crate24)
	(at pallet5 distributor2)
	(clear crate27)
	(at truck0 distributor1)
	(at truck1 depot0)
	(at hoist0 depot0)
	(available hoist0)
	(at hoist1 depot1)
	(available hoist1)
	(at hoist2 depot2)
	(available hoist2)
	(at hoist3 distributor0)
	(available hoist3)
	(at hoist4 distributor1)
	(available hoist4)
	(at hoist5 distributor2)
	(available hoist5)
	(at crate0 distributor2)
	(on crate0 pallet5)
	(at crate1 distributor1)
	(on crate1 pallet4)
	(at crate2 depot2)
	(on crate2 pallet2)
	(at crate3 distributor0)
	(on crate3 pallet3)
	(at crate4 distributor2)
	(on crate4 crate0)
	(at crate5 distributor1)
	(on crate5 crate1)
	(at crate6 distributor1)
	(on crate6 crate5)
	(at crate7 depot2)
	(on crate7 crate2)
	(at crate8 depot1)
	(on crate8 pallet1)
	(at crate9 depot1)
	(on crate9 crate8)
	(at crate10 depot2)
	(on crate10 crate7)
	(at crate11 distributor0)
	(on crate11 crate3)
	(at crate12 distributor2)
	(on crate12 crate4)
	(at crate13 depot2)
	(on crate13 crate10)
	(at crate14 depot0)
	(on crate14 pallet0)
	(at crate15 depot0)
	(on crate15 crate14)
	(at crate16 distributor2)
	(on crate16 crate12)
	(at crate17 depot0)
	(on crate17 crate15)
	(at crate18 depot2)
	(on crate18 crate13)
	(at crate19 distributor2)
	(on crate19 crate16)
	(at crate20 depot2)
	(on crate20 crate18)
	(at crate21 depot2)
	(on crate21 crate20)
	(at crate22 depot0)
	(on crate22 crate17)
	(at crate23 depot0)
	(on crate23 crate22)
	(at crate24 distributor1)
	(on crate24 crate6)
	(at crate25 distributor2)
	(on crate25 crate19)
	(at crate26 depot2)
	(on crate26 crate21)
	(at crate27 distributor2)
	(on crate27 crate25)
	(at crate28 depot0)
	(on crate28 crate23)
	(at crate29 depot1)
	(on crate29 crate9)
)

(:goal (and
		(on crate0 crate2)
		(on crate1 crate7)
		(on crate2 crate9)
		(on crate3 crate18)
		(on crate5 crate13)
		(on crate6 pallet2)
		(on crate7 crate12)
		(on crate9 pallet1)
		(on crate10 crate20)
		(on crate11 crate5)
		(on crate12 crate29)
		(on crate13 crate28)
		(on crate14 crate0)
		(on crate15 crate22)
		(on crate18 pallet3)
		(on crate19 crate10)
		(on crate20 crate3)
		(on crate21 pallet0)
		(on crate22 pallet5)
		(on crate23 crate21)
		(on crate24 crate14)
		(on crate25 crate19)
		(on crate27 crate24)
		(on crate28 pallet4)
		(on crate29 crate6)
	)
))
