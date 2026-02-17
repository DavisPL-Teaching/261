"""
=== Task scheduler ===

Given a list of tasks, including the time it takes to complete each task, the time until the deadline, and during what hour(s) it can be completed, is it possible to schedule the tasks in a way that we can complete all of them before the deadline?
If so, what's an example schedule?

=== Example input ===

Schedule start time: 8am (8)
Task: 1, 3 hours, 12 hours, 8am to 8pm
Task: 2, 2 hours, 10 hours, 8am to 8pm
Task: 3, 1 hour, 5 hours, 8am to 8pm

=== Example output ===

8am-9am: Task 3
9am-11am: Task 2
11am-2pm: Task 1

=== Design considerations ===

Let's assume that tasks are always scheduled in 1-hour blocks.
(1 hour is the smallest time unit here)

Will it always be possible?
No.

Is it possible there is space where we are doing nothing?
Yes

Do we always do one task in one contiguous block?
(For simplicity, let's say no for now.
but we could add it if we wanted to in a future update to our app.)
You have to do each task in one sitting.

What are we prioritizing?
What are we optimizing for here?
(For simplicity, let's set aside this q for now,
but we could add it if we wanted to in a future update to our app.)

=== 3 Steps ===

Let's first consider our three steps:

Remember: Think about the output, not the input.

1. What are the variables?
2. What are the constraints?
3. What are the properties we want to check?

1. What are the variables?

The tasks and the information about them
- how long they take, when you can do them, when they are due
(^ this one is input, not output)

Make a variable for each one hour chunk
^ 2nded

Make a variable for the first task that gets completed,
the second one, and so on.

a boolean?

Mapping of tasks to time that they are completed at?

For each task, what time should we start that task?
^
Let's go with the last one

Let's make a Python class for our scheduler.

API we have in mind:

    scheduler = Scheduler(start_time)
    scheduler.add_task(...)
    scheduler.add_task(...)
    scheduler.get_solution() # print solution
"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

class Task:
    """
    Task model
    """
    def __init__(self, schedule_start, name, duration, deadline):
        """
        Input parameters (regular Python variables)

        schedule_start: the start time for the entire schedule
        name: the name of the task
        duration: time it takes to complete
        deadline: time until task is due

        (Review: why are these regular Python variables?)
        """
        self.schedule_start = schedule_start
        self.name = name
        self.duration = duration
        self.deadline = deadline

        """
        Output parameters (Z3 variables)

        task_start: the time we start the task (time of day)
        task_end: the time we end the task (time of day)
        """
        self.task_start = z3.Int(f"{self.name} start")
        self.task_end = z3.Int(f"{self.name} end")

    def get_constraints(self):
        """
        Constraints that an individual task should satisfy.

        Return: Z3 formula
        """
        duration_constraint_1 = self.task_end == (
            self.task_start + self.duration
        )
        duration_constraint_2 = self.duration > 0
        deadline_constraint = (
            self.task_end <= self.schedule_start + self.deadline
        )
        schedule_start_constraint = self.task_start >= self.schedule_start

        # Return:
        return z3.And(
            duration_constraint_1,
            duration_constraint_2,
            deadline_constraint,
            schedule_start_constraint,
        )

    # Recap: we've written down the constraints for one individual task.
    # Next up: we also need to ensure that different tasks interact, and
    # in particular assert that different tasks do not overlap.

    ##### Where we left off for day 12

class Scheduler:
    """
    Scheduler interface
    """
    def __init__(self, schedule_start):
        self.schedule_start = schedule_start

        self.tasks = []
        self.constraints = []

    def get_constraints(self):
        # For each pair of tasks, check that the tasks do not overlap
        # --> i.e. the begin time of task1 is after the end time of task2,
        #     or vice versa.
        num_tasks = len(self.tasks)
        constraints = []
        for i in range(num_tasks):
            for j in range(i + 1, num_tasks):
                task1 = self.tasks[i]
                task2 = self.tasks[j]
                constraints.append(z3.Or(
                    task2.task_start >= task1.task_end,
                    task1.task_start >= task2.task_end,
                ))
        return constraints

    def add_task(
        self,
        task_name,
        task_duration,
        task_deadline,
        # Ignore these fields
        # available_hours_start, # between 0 and 24
        # available_hours_end, # between 0 and 24
    ):
        task = Task(self.schedule_start, task_name, task_duration, task_deadline)
        self.tasks.append(task)
        self.constraints.append(task.get_constraints())

        ##### Where we left off for day 11
        # To do next: add in the constraints here.

    def solve(self):
        # Combine all our constraints
        all_constraints = z3.And(self.constraints + self.get_constraints())
        result = solve(all_constraints)
        if result == SAT:
            print("A schedule was found!")
            # Not pretty printed -- but let's see what
            # it shows us
            print(get_solution(all_constraints))
        else:
            print("No schedule found")

# Example input
# Schedule start time: 8am (8)
# Task: 1, 3 hours, 12 hours, 8am to 8pm
# Task: 2, 2 hours, 10 hours, 8am to 8pm
# Task: 3, 1 hour, 5 hours, 8am to 8pm

schedule = Scheduler(8)
schedule.add_task("Go on hike", 3, 12)
schedule.add_task("Eat dinner", 2, 10)
schedule.add_task("Eat lunch", 1, 5)
schedule.solve()
