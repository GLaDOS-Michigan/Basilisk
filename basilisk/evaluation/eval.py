import csv
import os
import re
from file_sloc import count_sloc_between_tag, count_sloc_between_lines, count_patterns

EVAL_PATH = os.path.dirname(os.path.realpath(__file__))
PROTOCOL_LIST = "protocols.csv"
BASILISK_PROTOCOLS = f"{EVAL_PATH}/.."
KONDO_PROTOCOLS = f"{EVAL_PATH}/../../kondo"
OUTPUT_PATH = f"{EVAL_PATH}/sloc.csv"

def analyze_protocol(protocol_csv_file):
    with open(protocol_csv_file, 'r') as protocol_csv:
        csv_reader = csv.DictReader(protocol_csv)

        res = []
        res.append("protocol,basilisk_safety,basilisk_total,kondo_safety,kondo_total")

        auto_host_provs = 0
        for row in csv_reader:
            protocol = row['protocol']
            # hosts_spec = hosts_spec_sloc(protocol)
            # ds_spec = ds_spec_sloc(protocol)
            basilisk_safety, basilisk_total = basilisk_proof_sloc(protocol)

            # number_of_mono_invariants(protocol)
            auto_host_provs += number_of_host_prov_invariants(protocol)

            
            kondo_safety, kondo_total = -1, -1
            if row['in_kondo'] == 'true':
                # If this is a kondo protocol
                kondo_safety, kondo_total = kondo_proof_sloc(protocol, int(row['kondo_mods']))
                
            line = f"{protocol},{basilisk_safety},{basilisk_total},{kondo_safety},{kondo_total}"
            res.append(line)


        print(auto_host_provs)
    write_to_file(OUTPUT_PATH, "\n".join(res))

def hosts_spec_sloc(protocol):
    file_paths = [
        f"{BASILISK_PROTOCOLS}/{protocol}/hosts.dfy",
        f"{BASILISK_PROTOCOLS}/{protocol}/types.dfy",
        f"{BASILISK_PROTOCOLS}/{protocol}/automate_gen2/spec.dfy",
    ]
    spec_sloc = 0
    for fp in file_paths:
        spec_sloc += count_sloc_between_lines(fp, 1, 1000000)
    return spec_sloc

def ds_spec_sloc(protocol):
    file_path = f"{BASILISK_PROTOCOLS}/{protocol}/automate_gen2/distributedSystem.dfy"
    return count_sloc_between_lines(file_path, 1, 1000000) + hosts_spec_sloc(protocol)

def kondo_proof_sloc(protocol, safety_mods):
    file_path = f"{KONDO_PROTOCOLS}/{protocol}/sync/applicationProof.dfy"
    safety_proof = count_sloc_between_tag(file_path, "SAFETY PROOF")
    total_proof = count_sloc_between_lines(file_path, 1, 1000000)
    return safety_proof+safety_mods, total_proof+safety_mods

def basilisk_proof_sloc(protocol):
    file_path = f"{BASILISK_PROTOCOLS}/{protocol}/automate_gen2/applicationProofDemo.dfy"
    safety_proof = count_sloc_between_tag(file_path, "SAFETY PROOF")
    total_proof = count_sloc_between_lines(file_path, 1, 1000000)
    return safety_proof, total_proof

def number_of_mono_invariants(protocol):
    mono_file = f"{BASILISK_PROTOCOLS}/{protocol}/automate_gen2/monotonicityInvariantsAutogen.dfy"
    # msg_file = f"{BASILISK_PROTOCOLS}/{protocol}/automate_gen2/msgInvariantsAutogen.dfy"
    mono_invs = count_patterns(mono_file, re.compile(r'ghost predicate'))-1
    print(f"{protocol}: {mono_invs}")

def number_of_host_prov_invariants(protocol):
    # WARNING: THIS DOES NOT INCLUDE CUSTOM ONES
    msg_file = f"{BASILISK_PROTOCOLS}/{protocol}/automate_gen2/messageInvariantsAutogen.dfy"
    msg_invs = count_patterns(msg_file, re.compile(r'predicate [a-zA-Z0-9]+WitnessCondition'))
    # print(f"{protocol}: {msg_invs}")
    return msg_invs


def write_to_file(file_path, content):
    with open(file_path, 'w') as file:
        file.write(content)


def main():
    analyze_protocol(PROTOCOL_LIST)

if __name__ == "__main__":
    main()