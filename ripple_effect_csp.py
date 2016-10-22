from cspbase import *
import itertools

def ripple_effect_csp_model(initial_RP_board, rooms):
	'''
	Return a CSP object representing a Ripple Effect CSP problem
	along with an array of variables for the problem.

	RP_csp, var_array.

	Sample Board:
	[[ 0 , ' ',  3 , '|',  0 , ' ',  0 , '|' , 0 , '|',  1 , ' ',  0 , '|',  0 ],
	 [' ', ' ', ' ', '|', '-', ' ', '-', '|', ' ', '|', '-', ' ', '-', '|', ' '],
	 [ 2 , ' ',  0 , '|',  0 , '|',  3 , ' ',  0 , ' ',  6 , ' ',  0 , '|',  1 ],
	 ['-', ' ', '-', '|', '-', '|', '-', ' ', '-', ' ', '-', '|', ' ', '|', ' '],
	 [ 0 , '|',  0 , ' ',  0 , ' ',  0 , ' ',  0 , ' ',  4 , '|',  0 , '|',  0 ],
	 ['-', '|', ' ', '|', '-', ' ', '-', ' ', '-', ' ', '-', '|', '-', '|', ' '],
	 [ 3 , '|',  0 , '|',  2 , '|',  0 , '|',  0 , ' ',  0 , '|',  6 , '|',  3 ],
	 [' ', '|', '-', '|', ' ', '|', '-', '|', ' ', '|', '-', '|', ' ', '|', '-'],
	 [ 0 , '|',  0 , ' ',  0 , '|',  0 , ' ',  3 , '|',  5 , ' ',  2 , ' ',  0 ],
	 [' ', '|', ' ', '|', '-', '|', ' ', ' ', ' ', '|', '-', '|', ' ', ' ', ' '],
	 [ 0 , '|',  3 , '|',  0 , '|',  5 , ' ',  0 , '|',  1 , '|',  0 , ' ',  0 ],
	 [' ', '|', '-', '|', ' ', '|', '-', ' ', '-', '|', ' ', '|', '-', ' ', '-'],
	 [ 0 , '|',  0 , '|',  0 , '|',  3 , ' ',  5 , ' ',  0 , ' ',  0 , '|',  0 ],
	 ['-', '|', ' ', '|', '-', '|', '-', ' ', '-', ' ', '-', ' ', '-', '|', ' '],
	 [ 0 , '|',  0 , '|',  3 , ' ',  0 , ' ',  0 , ' ',  0 , '|',  0 , '|',  0 ]]
	'''
	# Find size of the board M x N
	M = (len(initial_RP_board[0]) + 1) // 2	# width
	N = (len(initial_RP_board) + 1) // 2	# height

	# Make Variable Array
	var_array = make_variable(initial_RP_board, rooms, M, N)

	# Make Constraints
	# Each room must have n-ary all-diff constraints
	room_cons = [room_constraint(var_array, room, k+1) for k, room in enumerate(rooms)]

	max_rsize = max([len(room) for room in rooms])
	space_cons = space_constraint(var_array, max_rsize, M, N)

	# Create csp
	csp = CSP("Ripple_Effect")
	# Add varaibels
	for row in var_array:
		for var in row:
			csp.add_var(var)
	# Add rooms
	for room in rooms:
		csp.add_room(room)
	# Add constraints
	for cons in room_cons:
		csp.add_constraint(cons)
	for cons in space_cons:
		csp.add_constraint(cons)

	return csp, var_array

def make_variable(board, rooms, M, N):
	# Make all of MxN variables in a board format (list of list of Variable)
	var_array = [[Variable( "V{},{}".format(i, j) ) for j in range(M)] for i in range(N)]
	# for each room provided, find the domain and add it to each variable.
	# if a cell is provided with a value, assign that value to the variable accordingly
	for room in rooms:
		max_domain = len(room) # maximum value possible
		for cell in room:
			i, j = cell
			var = var_array[i][j] # Variable
			var.add_domain_values([(n+1) for n in range(max_domain)]) # add domains
			val = board[i * 2][j * 2] # value from the board
			if val != 0: # and val < max_domain: is error checking necessary?
				var.assign(val) # assign value
				var.domain = [val]

	return var_array

def room_constraint(var_array, room, k):
	# make n-ary all diff constraint for k-th room
	it = [(n+1) for n in range(len(room))]

	# find scope
	scope = []
	for i, j in room:
		scope.append(var_array[i][j])

	# remove already assigned values, no need to perform permutation with them.
	# this is for faster performance.
	found = []
	for i, var in enumerate(scope):
		if var.is_assigned():
			found.append((i, var.get_assigned_value()))
			it.remove(var.get_assigned_value())

	# Find all satisfying tuples
	sat_tuples = [list(L) for L in itertools.permutations(it)]
	# add already assigned values
	for i, val in found:
		for tup in sat_tuples:
			tup.insert(i, val)

	# Create new constraint and add scope & sat_tuples
	c = Constraint("C{}".format(k), scope)
	c.add_satisfying_tuples(sat_tuples)

	# Return the constraint
	return c

def space_constraint(var_array, max_rsize, M, N):
	# create satisfying tuples for differently distanced variables
	n_dist_tuples = [list(itertools.product(range(1, max_rsize+1), repeat=2)) for i in range(max_rsize)]
	for n in range(max_rsize):
		for t in zip(range(n+1, max_rsize+1), range(n+1, max_rsize+1)):
			n_dist_tuples[n].remove(t)

	# create binary constraints for different combinations of variables in row
	space_cons = []
	for i in range(N):
		for a, b in itertools.product(range(M), repeat=2):
			for n in range(max_rsize):
				if abs(a - b) == n+1:
					con_row = make_constraint(var_array[i][a], var_array[i][b])
					con_row.add_satisfying_tuples(n_dist_tuples[n])
					space_cons.append(con_row)

	# create binary constraints for different combinations of variables in col
	for i in range(M):
		for a, b in itertools.product(range(N), repeat=2):
			for n in range(max_rsize):
				if abs(a - b) == n+1:
					con_col = make_constraint(var_array[a][i], var_array[b][i])
					con_col.add_satisfying_tuples(n_dist_tuples[n])
					space_cons.append(con_col)
	return space_cons

def make_constraint(var1, var2):
	return Constraint('C-{}:{}'.format(var1.name, var2.name), [var1, var2])

