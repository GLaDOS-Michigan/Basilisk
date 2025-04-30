import sys
import re

def count_sloc_between_tag(file_path, tag):
    start_tag = "BEGIN " + tag
    end_tag = "END " + tag

    start_line, end_line = -1, -1

    with open(file_path, 'r') as file:
        for line_number, line in enumerate(file, start=1):
            if start_tag in line:
                if start_line >= 0:
                    raise KeyError(f"Start tag {tag} already encountered")
                start_line = line_number
            if end_tag in line:
                if end_line >= 0:
                    raise KeyError(f"End tag {tag} already encountered")
                end_line = line_number
    
    if start_line < 0 or end_line < 0:
        raise KeyError(f"Tag pairs not found for {tag}")

    if start_line > end_line:
        raise KeyError(f"Invalid ordering for {tag}")

    return count_sloc_between_lines(file_path, start_line, end_line)


def count_sloc_between_lines(file_path, start_line, end_line):
    with open(file_path, 'r') as file:
        lines = file.readlines()

    sloc_count = 0
    in_comment_block = False

    for i, line in enumerate(lines, start=1):
        # Remove leading and trailing whitespaces
        stripped_line = line.strip()

        # Check if the line is part of a multi-line comment
        if '/*' in stripped_line:
            in_comment_block = True

        if not in_comment_block and start_line <= i <= end_line:
            # Check if the line is not a comment or blank
            if stripped_line and not stripped_line.startswith('//'): 
                sloc_count += 1

        if '*/' in stripped_line:
            in_comment_block = False

    return sloc_count

def count_patterns(file_path, pattern):
    match_count = 0
    with open(file_path, 'r') as file:
        for line in file:
            if pattern.search(line):  # Use search() to find a match in the line
                match_count += 1
    return match_count

def main():
    if len(sys.argv) != 3:
        print("Usage: python count_sloc.py <file_path> <tag>")
        sys.exit(1)

    file_path = sys.argv[1]
    tag = sys.argv[2]

    sloc = count_sloc_between_tag(file_path, tag)
    print(f'The number of Source Lines of Code (SLOC) for tag {tag} is: {sloc}')

if __name__ == "__main__":
    main()
