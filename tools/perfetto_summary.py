#!/usr/bin/env python3
"""Summarize a trace the `tracing` feature writes (lunacy.fxt), read with
Perfetto's trace processor as Perfetto's UI reads it: its tracks, slices and
events, and its JIT bailouts by reason and by where they are.

    tools/perfetto_summary.py working/lunacy.fxt

(in the devshell, whose `trace_processor_shell` it runs; `just trace` runs it)
"""
import shutil
import sys
from perfetto.trace_processor import TraceProcessor, TraceProcessorConfig

def verify_trace(filename):
    try:
        # TraceProcessor can take a while to load large traces
        tp = TraceProcessor(trace=filename, config=TraceProcessorConfig(bin_path=shutil.which('trace_processor_shell')))
        print(f"Successfully loaded trace: {filename}")

        # Check for tracks
        qr = tp.query("SELECT count(*) as cnt FROM track")
        track_count = next(qr).cnt
        print(f"Number of tracks: {track_count}")

        # Check for slices
        qr = tp.query("SELECT count(*) as cnt FROM slice")
        slice_count = next(qr).cnt
        print(f"Number of slices: {slice_count}")

        # Check for threads
        qr = tp.query("SELECT count(*) as cnt FROM thread")
        thread_count = next(qr).cnt
        print(f"Number of threads: {thread_count}")

        # Check for process
        qr = tp.query("SELECT count(*) as cnt FROM process")
        process_count = next(qr).cnt
        print(f"Number of processes: {process_count}")

        if slice_count > 0 or track_count > 0:
            print("Trace seems valid and contains data.")

            # Print a summary
            print("\n--- Trace Summary ---")
            qr = tp.query("SELECT category, name, count(*) as cnt FROM slice GROUP BY category, name ORDER BY cnt DESC")
            print(f"{'Category':<15} | {'Name':<20} | {'Count':<10}")
            print("-" * 50)
            for row in qr:
                print(f"{row.category:<15} | {row.name:<20} | {row.cnt:<10}")

            print("\n--- JIT Bailout Reasons ---")
            qr = tp.query("""
                SELECT
                    args.display_value as reason,
                    count(*) as cnt
                FROM slice
                JOIN args ON slice.arg_set_id = args.arg_set_id
                WHERE slice.category = 'jit' AND slice.name = 'bailout' AND args.key = 'reason'
                GROUP BY reason
                ORDER BY cnt DESC
            """)
            print(f"{'Reason':<25} | {'Count':<10}")
            print("-" * 40)
            for row in qr:
                print(f"{row.reason:<25} | {row.cnt:<10}")

            print("\n--- JIT Bailouts by Reason, Function and Block ---")
            qr = tp.query("""
                SELECT
                    extract_arg(slice.arg_set_id, 'reason') as reason,
                    extract_arg(slice.arg_set_id, 'source') as source,
                    extract_arg(slice.arg_set_id, 'line') as line,
                    extract_arg(slice.arg_set_id, 'block_id') as block,
                    count(*) as cnt
                FROM slice
                WHERE slice.category = 'jit' AND slice.name = 'bailout'
                GROUP BY reason, source, line, block
                ORDER BY cnt DESC
                LIMIT 20
            """)
            for row in qr:
                print(f"{row.cnt:>10} | {str(row.reason):<30} | {row.source}:{row.line} block {row.block}")
        else:
            print("Trace loaded but seems empty of slices/tracks.")

    except Exception as e:
        print(f"Failed to load trace with perfetto TraceProcessor: {e}")
        # Try to read the first few bytes to see if it's even FXT
        try:
            with open(filename, 'rb') as f:
                header = f.read(8)
                print(f"First 8 bytes of file: {header.hex()}")
        except:
            pass
        sys.exit(1)

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 verify_perfetto.py <filename>")
    else:
        verify_trace(sys.argv[1])
