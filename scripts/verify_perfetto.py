import sys
from perfetto.trace_processor import TraceProcessor

def verify_trace(filename):
    try:
        # TraceProcessor can take a while to load large traces
        tp = TraceProcessor(file_path=filename)
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
