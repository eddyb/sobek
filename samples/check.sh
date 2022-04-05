#!/usr/bin/env bash

set -e

# Pre-build `sobek` and ensure the resulting executable runs.
sobek="target/release/sobek"
cargo build --release
"$sobek" --help > /dev/null

# Styles.
Sreset=$(tput sgr0)
Sbold=$(tput bold)
Sunderline=$(tput smul)
Serr=$(tput setaf 9)
Swarn=$(tput setaf 11)

sample() {
    local platform="$1"
    local rom_filename="$2"
    shift 2
    local flags=("$@")

    local name rom log
    name=$(echo "$rom_filename" | sed -E 's/\.[a-z0-9]+$//')
    rom="samples/$platform/$rom_filename"
    log="samples/$platform/$name.log"

    echo
    echo "$Sbold""$Sunderline""# $name ($platform)""$Sreset"

    # Compare log.new and log, and collapse them if they're identical.
    #
    # Defined here so it can also be attempted before running `sobek`
    # (if preexisting files exist, including from previous runs).
    check_log() {
        if [ -f "$log" ] && (! cmp --quiet "$log"{,.new}); then
            if [ -n "$BLESS_FIRST" ]; then
                mv --backup=numbered --verbose "$log"{,.old}
                unset BLESS_FIRST
            else
                echo "$Serr""    $log.new differs from $log""$Sreset"
                ([ -n "$DIFF_TOOL" ] && $DIFF_TOOL "$log"{,.new}) || true
                echo "    Run \`BLESS_FIRST=1 $0\` to accept this change"
                exit 1
            fi
        fi

        mv "$log"{.new,}
    }

    if [ -f "$log".new ]; then
        echo "$Swarn""    Found preexisting $log.new, checking...""$Sreset"
        check_log
    fi

    # Only run `sobek` if anything has changed since the last time.
    if [ "$log" -nt "$sobek" ] && [ "$log" -nt samples/samples.sh ] && [ "$log" -nt "$rom" ]; then
        echo "    Skipping ($log is fresh according to mtime)..."
    else
        "$sobek" -p "$platform" "$rom" "${flags[@]}" > "$log".new
        check_log
    fi
}

# All `sample` invocations are in a separate (`.gitignore`d) file.
if ! [ -f samples/samples.sh ]; then
    echo "$Serr""Missing samples/samples.sh""$Sreset"
    echo "    Create \`samples/samples.sh\` and add to it commands like this:"
    echo "        sample n64 foo.rom"
    echo "    to have \`sobek n64 samples/n64/foo.rom\` be tested by this script"
    exit 1
fi
source samples/samples.sh
