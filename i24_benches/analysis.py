#!/usr/bin/env python3
"""
Comprehensive analysis and visualization of i24 benchmark results.

This script processes the JSON output from the i24 benchmark tool,
generates detailed visualizations, and produces formatted markdown tables
for easy inclusion in documentation or reports.

Make sure to have the required libraries installed:
```
pip install pandas matplotlib seaborn tabulate numpy
```
"""

import json
import matplotlib.pyplot as plt
import pandas as pd
import numpy as np
import seaborn as sns
from pathlib import Path
import argparse
from tabulate import tabulate
import sys
from datetime import datetime
import re

# Set Seaborn style for better-looking plots
sns.set_theme(style="whitegrid")

def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(description="Analyze i24 benchmark results")
    parser.add_argument("--input", "-i", default="i24_benchmark_results.json",
                        help="Path to benchmark results JSON file")
    parser.add_argument("--output", "-o", default="benchmark_analysis",
                        help="Output directory for reports and visualizations")
    parser.add_argument("--format", "-f", choices=["png", "svg", "pdf"], default="png",
                        help="Output format for visualizations")
    parser.add_argument("--dpi", type=int, default=300,
                        help="DPI for output images")
    return parser.parse_args()

def load_benchmark_data(filepath):
    """Load benchmark data from JSON file."""
    try:
        with open(filepath, 'r') as f:
            data = json.load(f)
        return data
    except FileNotFoundError:
        print(f"Error: Benchmark file {filepath} not found.")
        sys.exit(1)
    except json.JSONDecodeError:
        print(f"Error: Failed to parse {filepath} as JSON.")
        sys.exit(1)

def preprocess_data(data):
    """Process raw benchmark data into useful DataFrames."""
    # Convert results to a DataFrame
    df = pd.DataFrame(data["results"])
    
    # Extract operation categories
    df['operation_category'] = df['operation'].apply(categorize_operation)
    
    # Create pivot tables for different analyses
    pivot_throughput = df.pivot(index='operation', columns='operand_type', values='throughput')
    pivot_duration = df.pivot(index='operation', columns='operand_type', values='duration_ns')
    
    # Calculate performance ratios
    performance_df = pd.DataFrame()
    
    # Throughput ratio (higher is better for i24)
    if 'i24' in pivot_throughput.columns and 'i32' in pivot_throughput.columns:
        performance_df['throughput_ratio'] = pivot_throughput['i24'] / pivot_throughput['i32']
    
    # Duration ratio (lower is better for i24)
    if 'i24' in pivot_duration.columns and 'i32' in pivot_duration.columns:
        performance_df['duration_ratio'] = pivot_duration['i24'] / pivot_duration['i32']
    
    # Add operation categories
    operation_categories = {op: categorize_operation(op) for op in performance_df.index}
    performance_df['category'] = performance_df.index.map(operation_categories)
    
    return {
        'raw': df,
        'throughput': pivot_throughput,
        'duration': pivot_duration,
        'performance': performance_df,
        'system_info': data['system_info'],
        'timestamp': data['timestamp']
    }

def categorize_operation(operation_name):
    """Categorize operations into groups."""
    if re.match(r'Add|Sub|Mul|Div|Rem', operation_name):
        return 'Arithmetic'
    elif re.match(r'BitAnd|BitOr|BitXor|BitwiseNot', operation_name):
        return 'Bitwise'
    elif re.match(r'LeftShift|RightShift', operation_name):
        return 'Shift'
    elif re.match(r'Neg', operation_name):
        return 'Unary'
    elif re.match(r'FromI32|ToI32|ByteConversion', operation_name):
        return 'Conversion'
    else:
        return 'Other'

def plot_throughput_comparison(data, output_dir, img_format, dpi):
    """Create a bar chart comparing throughput between i24 and i32."""
    throughput_df = data['throughput']
    
    # Filter only operations that have both i24 and i32 implementations
    operations = []
    for op in throughput_df.index:
        if 'i24' in throughput_df.columns and 'i32' in throughput_df.columns:
            if not pd.isna(throughput_df.loc[op, 'i24']) and not pd.isna(throughput_df.loc[op, 'i32']):
                operations.append(op)
    
    if not operations:
        print("Warning: No comparable operations found for throughput")
        return
    
    # Categorize operations
    categories = [categorize_operation(op) for op in operations]
    category_colors = {
        'Arithmetic': '#1f77b4',  # blue
        'Bitwise': '#ff7f0e',     # orange
        'Shift': '#2ca02c',       # green
        'Unary': '#d62728',       # red
        'Conversion': '#9467bd',  # purple
        'Other': '#8c564b'        # brown
    }
    
    i24_colors = [category_colors[cat] for cat in categories]
    i32_colors = [sns.desaturate(color, 0.6) for color in i24_colors]
    
    # Set up the figure
    plt.figure(figsize=(14, 8))
    
    # Create positions for the bars
    x = np.arange(len(operations))
    width = 0.35
    
    # Create bars
    i24_throughput = [throughput_df.loc[op, 'i24'] for op in operations]
    i32_throughput = [throughput_df.loc[op, 'i32'] for op in operations]
    
    # Plot bars
    plt.bar(x - width/2, i24_throughput, width, label='i24', color=i24_colors)
    plt.bar(x + width/2, i32_throughput, width, label='i32', color=i32_colors)
    
    # Add labels and title
    plt.ylabel('Operations per second', fontsize=12)
    plt.title('Throughput Comparison: i24 vs i32', fontsize=14)
    plt.xticks(x, operations, rotation=45, ha='right')
    plt.legend(fontsize=12)
    
    # Add a grid for better readability
    plt.grid(axis='y', linestyle='--', alpha=0.7)
    
    # Format y-axis with commas for thousands
    plt.gca().yaxis.set_major_formatter(plt.FuncFormatter(lambda x, _: f'{x:,.0f}'))
    
    # Add values above bars
    for i, (i24_val, i32_val) in enumerate(zip(i24_throughput, i32_throughput)):
        plt.text(i - width/2, i24_val + max(i24_throughput) * 0.02, f'{i24_val:,.0f}', 
                 ha='center', va='bottom', fontsize=8, rotation=45)
        plt.text(i + width/2, i32_val + max(i32_throughput) * 0.02, f'{i32_val:,.0f}', 
                 ha='center', va='bottom', fontsize=8, rotation=45)
    
    # Adjust layout and save
    plt.tight_layout()
    plt.savefig(f"{output_dir}/throughput_comparison.{img_format}", dpi=dpi)
    print(f"Created throughput comparison chart: {output_dir}/throughput_comparison.{img_format}")
    plt.close()

def plot_relative_performance(data, output_dir, img_format, dpi):
    """Create a plot showing relative performance of i24 compared to i32."""
    performance_df = data['performance']
    
    if 'throughput_ratio' not in performance_df.columns:
        print("Warning: No throughput ratio data available")
        return
    
    # Sort operations by category and then by performance ratio
    sorted_df = performance_df.sort_values(['category', 'throughput_ratio'], ascending=[True, False])
    
    # Drop NaN values
    sorted_df = sorted_df.dropna(subset=['throughput_ratio'])
    
    if sorted_df.empty:
        print("Warning: No valid data for performance ratio plot")
        return
    
    # Set up plot
    plt.figure(figsize=(12, 10))
    
    # Create horizontal bar chart
    operations = sorted_df.index
    ratios = sorted_df['throughput_ratio']
    categories = sorted_df['category']
    
    # Define colors based on performance and category
    category_colors = {
        'Arithmetic': '#1f77b4',  # blue
        'Bitwise': '#ff7f0e',     # orange
        'Shift': '#2ca02c',       # green
        'Unary': '#d62728',       # red
        'Conversion': '#9467bd',  # purple
        'Other': '#8c564b'        # brown
    }
    
    colors = [category_colors[cat] if r >= 1.0 else sns.desaturate(category_colors[cat], 0.6) 
              for cat, r in zip(categories, ratios)]
    
    # Create y-position for each operation
    y_pos = np.arange(len(operations))
    
    # Plot horizontal bars
    bars = plt.barh(y_pos, ratios, color=colors)
    
    # Add a vertical line at 1.0
    plt.axvline(x=1.0, color='black', linestyle='--', alpha=0.7)
    
    # Add labels
    plt.xlabel('Performance Ratio (i24 / i32)', fontsize=12)
    plt.title('Relative Performance of i24 compared to i32', fontsize=14)
    plt.yticks(y_pos, operations)
    
    # Add actual values as text
    for i, v in enumerate(ratios):
        text_color = 'black' if v < 1.0 else 'white'
        plt.text(max(v + 0.05, 1.05), i, f"{v:.2f}x", va='center', color=text_color)
    
    # Add category dividers and labels
    last_category = None
    category_positions = []
    
    for i, (op, cat) in enumerate(zip(operations, categories)):
        if cat != last_category:
            if i > 0:
                plt.axhline(y=i-0.5, color='gray', linestyle='-', alpha=0.3, linewidth=1)
            last_category = cat
            category_positions.append((i, cat))
    
    # Add category labels
    for pos, cat in category_positions:
        plt.text(-0.15, pos, cat, rotation=90, ha='center', va='bottom', 
                 fontweight='bold', color=category_colors[cat])
    
    # Adjust layout and save
    plt.tight_layout()
    plt.subplots_adjust(left=0.2)  # Make room for category labels
    plt.savefig(f"{output_dir}/relative_performance.{img_format}", dpi=dpi)
    print(f"Created relative performance chart: {output_dir}/relative_performance.{img_format}")
    plt.close()

def plot_performance_by_category(data, output_dir, img_format, dpi):
    """Create a boxplot showing performance distribution by operation category."""
    performance_df = data['performance'].copy()
    
    if 'throughput_ratio' not in performance_df.columns or 'category' not in performance_df.columns:
        print("Warning: Missing data for category performance plot")
        return
    
    # Drop NaN values
    performance_df = performance_df.dropna(subset=['throughput_ratio'])
    
    if performance_df.empty:
        print("Warning: No valid data for category performance plot")
        return
    
    # Set up plot
    plt.figure(figsize=(10, 6))
    
    # Create boxplot
    sns.boxplot(x='category', y='throughput_ratio', data=performance_df)
    
    # Add a horizontal line at 1.0
    plt.axhline(y=1.0, color='red', linestyle='--', alpha=0.7)
    
    # Add labels
    plt.xlabel('Operation Category', fontsize=12)
    plt.ylabel('Performance Ratio (i24 / i32)', fontsize=12)
    plt.title('Performance Distribution by Operation Category', fontsize=14)
    
    # Adjust layout and save
    plt.tight_layout()
    plt.savefig(f"{output_dir}/performance_by_category.{img_format}", dpi=dpi)
    print(f"Created category performance chart: {output_dir}/performance_by_category.{img_format}")
    plt.close()

def plot_operation_durations(data, output_dir, img_format, dpi):
    """Create a log-scale plot comparing operation durations."""
    duration_df = data['duration'].copy()
    
    # Filter only operations that have both i24 and i32 implementations
    operations = []
    for op in duration_df.index:
        if 'i24' in duration_df.columns and 'i32' in duration_df.columns:
            if not pd.isna(duration_df.loc[op, 'i24']) and not pd.isna(duration_df.loc[op, 'i32']):
                operations.append(op)
    
    if not operations:
        print("Warning: No comparable operations found for duration plot")
        return
    
    # Convert to nanoseconds per operation for easier comparison
    duration_df = duration_df.loc[operations]
    
    # Set up plot
    plt.figure(figsize=(12, 8))
    
    # Create log-scale plot
    plt.semilogy(duration_df.index, duration_df['i24'], 'o-', label='i24')
    plt.semilogy(duration_df.index, duration_df['i32'], 'o-', label='i32')
    
    # Add labels
    plt.ylabel('Duration per Operation (ns, log scale)', fontsize=12)
    plt.title('Operation Duration Comparison (lower is better)', fontsize=14)
    plt.xticks(rotation=45, ha='right')
    plt.legend()
    
    # Add grid for better readability
    plt.grid(True, which="both", ls="-", alpha=0.2)
    
    # Adjust layout and save
    plt.tight_layout()
    plt.savefig(f"{output_dir}/operation_durations.{img_format}", dpi=dpi)
    print(f"Created operation durations chart: {output_dir}/operation_durations.{img_format}")
    plt.close()

def generate_markdown_report(data, output_dir):
    """Generate a comprehensive markdown report with benchmark results."""
    system_info = data['system_info']
    performance_df = data['performance'].copy()
    throughput_df = data['throughput'].copy()
    duration_df = data['duration']
    
    # Format DataFrames for the report
    if not performance_df.empty:
        # Format the ratio columns
        if 'throughput_ratio' in performance_df.columns:
            performance_df['throughput_ratio'] = performance_df['throughput_ratio'].map(lambda x: f"{x:.2f}x" if not pd.isna(x) else np.nan)
        if 'duration_ratio' in performance_df.columns:
            performance_df['duration_ratio'] = performance_df['duration_ratio'].map(lambda x: f"{x:.2f}x" if not pd.isna(x) else np.nan)
    
    # Format throughput values with commas
    for col in throughput_df.columns:
        throughput_df[col] = throughput_df[col].map(lambda x: f"{x:,.0f}" if not pd.isna(x) else np.nan)
    
    # Format duration values
    for col in duration_df.columns:
        duration_df[col] = duration_df[col].map(lambda x: f"{x:.3f}" if not pd.isna(x) else  np.nan)
    
    # Create the markdown content
    markdown = []
    
    # Title and metadata
    markdown.extend([
        "# i24 Benchmark Results\n",
        f"*Generated on: {data['timestamp']}*\n",
        "## System Information\n",
        f"- **CPU:** {system_info['cpu_info']}",
        f"- **Memory:** {system_info['memory_mb']} MB",
        f"- **OS:** {system_info['os']}",
        f"- **Rust Version:** {system_info['rust_version']}\n",
    ])
    
    # Executive summary
    if 'throughput_ratio' in performance_df.columns:
        better_count = sum(performance_df['throughput_ratio'].str.rstrip('x').astype(float) >= 1.0)
        worse_count = sum(performance_df['throughput_ratio'].str.rstrip('x').astype(float) < 1.0)
        best_op = performance_df['throughput_ratio'].str.rstrip('x').astype(float).idxmax()
        best_ratio = performance_df.loc[best_op, 'throughput_ratio']
        worst_op = performance_df['throughput_ratio'].str.rstrip('x').astype(float).idxmin()
        worst_ratio = performance_df.loc[worst_op, 'throughput_ratio']
        
        markdown.extend([
            "## Executive Summary\n",
            f"- i24 performs better than i32 in **{better_count}** operations and worse in **{worse_count}** operations.",
            f"- Best relative performance: **{best_op}** ({best_ratio} of i32 performance)",
            f"- Worst relative performance: **{worst_op}** ({worst_ratio} of i32 performance)\n",
        ])
    
    # Performance by category
    if 'category' in performance_df.columns and 'throughput_ratio' in performance_df.columns:
        markdown.append("## Performance by Category\n")
        
        # Group by category and calculate average performance
        category_perf = performance_df.copy()
        category_perf['ratio_value'] = category_perf['throughput_ratio'].str.rstrip('x').astype(float)
        category_avg = category_perf.groupby('category')['ratio_value'].mean().sort_values(ascending=False)
        
        # Create category summary table
        category_table = []
        for cat, avg in category_avg.items():
            category_table.append([cat, f"{avg:.2f}x"])
        
        markdown.append(tabulate(category_table, headers=["Category", "Average Performance"], tablefmt="pipe"))
        markdown.append("\n")
    
    # Detailed benchmark results
    markdown.append("## Detailed Benchmark Results\n")
    
    # Throughput table
    markdown.append("### Throughput (Operations per second)\n")
    throughput_reset = throughput_df.reset_index()
    markdown.append(tabulate(throughput_reset, headers='keys', tablefmt="pipe", showindex=False))
    markdown.append("\n")
    
    # Duration table
    markdown.append("### Duration (nanoseconds per operation)\n")
    duration_reset = duration_df.reset_index()
    markdown.append(tabulate(duration_reset, headers='keys', tablefmt="pipe", showindex=False))
    markdown.append("\n")
    
    # Relative performance table
    markdown.append("### Relative Performance (i24 vs i32)\n")
    if not performance_df.empty:
        perf_reset = performance_df.reset_index()[['operation', 'throughput_ratio', 'duration_ratio', 'category']]
        perf_reset.columns = ['Operation', 'Throughput Ratio', 'Duration Ratio', 'Category']
        markdown.append(tabulate(perf_reset, headers='keys', tablefmt="pipe", showindex=False))
        markdown.append("\n")
    
    # Best and worst performers
    markdown.append("## Performance Highlights\n")
    
    if 'throughput_ratio' in performance_df.columns:
        # Convert string ratios back to float for sorting
        performance_df['ratio_value'] = performance_df['throughput_ratio'].str.rstrip('x').astype(float)
        
        # Top 5 best performers
        markdown.append("### Top 5 Best Performers\n")
        top5 = performance_df.sort_values('ratio_value', ascending=False).head(5)
        top5_table = top5.reset_index()[['operation', 'throughput_ratio', 'category']]
        top5_table.columns = ['Operation', 'Performance Ratio', 'Category']
        markdown.append(tabulate(top5_table, headers='keys', tablefmt="pipe", showindex=False))
        markdown.append("\n")
        
        # Bottom 5 worst performers
        markdown.append("### Bottom 5 Worst Performers\n")
        bottom5 = performance_df.sort_values('ratio_value', ascending=True).head(5)
        bottom5_table = bottom5.reset_index()[['operation', 'throughput_ratio', 'category']]
        bottom5_table.columns = ['Operation', 'Performance Ratio', 'Category']
        markdown.append(tabulate(bottom5_table, headers='keys', tablefmt="pipe", showindex=False))
        markdown.append("\n")
    
    # Write the report to file
    report_path = f"{output_dir}/benchmark_report.md"
    with open(report_path, "w") as f:
        f.write("\n".join(markdown))
    
    print(f"Generated markdown report: {report_path}")
    
    return "\n".join(markdown)

def main():
    """Main function to process benchmark data, create visualizations and reports."""
    # Parse command line arguments
    args = parse_args()
    
    # Create output directory
    output_dir = args.output
    Path(output_dir).mkdir(exist_ok=True, parents=True)
    
    print(f"Loading benchmark data from {args.input}...")
    data = load_benchmark_data(args.input)
    
    print("Processing benchmark data...")
    processed_data = preprocess_data(data)
    
    print("Generating visualizations...")
    plot_throughput_comparison(processed_data, output_dir, args.format, args.dpi)
    plot_relative_performance(processed_data, output_dir, args.format, args.dpi)
    plot_performance_by_category(processed_data, output_dir, args.format, args.dpi)
    plot_operation_durations(processed_data, output_dir, args.format, args.dpi)
    
    print("Generating markdown report...")
    report = generate_markdown_report(processed_data, output_dir)
    
    print(f"Analysis complete! Results saved to {output_dir}/")

if __name__ == "__main__":
    main()