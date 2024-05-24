import LogicCircuits
import DelimitedFiles

function sizeBDD(fp)
	bdd = LogicCircuits.Bdd
	results = @timed LogicCircuits.load_cnf(bdd, fp)
	bdd = results[1]
	time = results[2]
	size = LogicCircuits.size(bdd)
	return size, time
end

function sizeSDD(fp)
	circuit = LogicCircuits.PlainLogicCircuit
	nnfFormat = LogicCircuits.NnfFormat()
	results = @timed LogicCircuits.read(fp, circuit, nnfFormat)
	sdd = results[1]
	time = results[2]
	size = LogicCircuits.sdd_size(sdd)
	return size, time
end

function sizeSDDSmooth(fp)
	circuit = LogicCircuits.PlainLogicCircuit
	nnfFormat = LogicCircuits.NnfFormat()
	results = @timed LogicCircuits.smooth(LogicCircuits.read(fp, circuit, nnfFormat))
	sdd = results[1]
	time = results[2]
	size = LogicCircuits.sdd_size(sdd)
	return size, time
end

experiments = [ "argumentation", "hmm", "montyhall", "simple" ]

path = "../programs/"
bdd_files = [ filter(x->endswith(x, ".cnf"), readdir(path * type, join=true)) for type in experiments ]
bdd_files = [ name for type in bdd_files for name in type ]
sdd_files = [ filter(x->endswith(x, ".nnf"), readdir(path * type, join=true)) for type in experiments ]
sdd_files = [ name for type in sdd_files for name in type ]

nrows = length(bdd_files)
zipped = zip(2:nrows+1, bdd_files, sdd_files)

all_sizes = Array{Any, 2}(undef, nrows+1, 4)
all_times = Array{Any, 2}(undef, nrows+1, 4)

all_sizes[1, :] .= [ "Sizes", "BDD", "SDD", "SDD_Smooth" ]

all_times[1, :] .= [ "Times", "BDD", "SDD", "SDD_Smooth" ]

for (i, fp_bdd, fp_sdd) in zipped

	sizes = Array{Any, 1}(undef, 4)
	times = Array{Any, 1}(undef, 4)
	
	str_len = length(fp_bdd)
	last_slash = last(findlast("/", fp_bdd))
	program_name = fp_bdd[last_slash+1:str_len]

	sizes[1] = program_name
	times[1] = program_name

	sizes[2], times[2] = sizeBDD(fp_bdd)
	sizes[3], times[3] = sizeSDD(fp_sdd)
	sizes[4], times[4] = sizeSDDSmooth(fp_sdd)
	
	println("$program_name:")
	println("	Sizes = $sizes")
	println("	Times = $times")

	all_sizes[i, :] .= sizes
	all_times[i, :] .= times
end

DelimitedFiles.writedlm("Sizes.csv",  all_sizes, ',')
DelimitedFiles.writedlm("Times.csv",  all_times, ',')
