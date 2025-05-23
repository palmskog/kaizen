import sys

def setup_json_file(num_workers):
	i = 1;
	json_obj = { "nodes" : [] }
	while (i <= num_workers):
		local_obj = {
		"id": i,
        "ip_address": "10.1.1." + str(i + 2),
      	"port": 9050,
      	"address": "2MuYvxnCgBmrPHaBcaYQrtGZ4MpzMEakAzS",
      	"key": "cNCC6KBjMN35wABHknBgEcQHfq7AVF8fmN8Vy3J224JNz4CVsU8F",
      	"unspent_transactions": "data/experiments/listunspent"+str(i)+".json"
		}
		json_obj["nodes"].insert(0, local_obj)
		i += 1;
	print json_obj;


def main():
	if (len(sys.argv) < 2):
		print "Usage python cluster_setup.py <num_workers>" #jobMetrics.txt
		exit(1)	
	
	setup_json_file(int(sys.argv[1]));


if __name__ == "__main__":
    main()