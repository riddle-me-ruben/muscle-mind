from flask import request, redirect, url_for, render_template

class QuizManager:
    def __init__(self, db_manager):
        self.db_manager = db_manager

    # Function to render the quiz creation form based on user input for the number of questions
    def create_quiz(self):
        num_questions = request.form.get('num_questions')  # Safely get the number of questions
        title = request.form.get('title')
        if num_questions:
            num_questions = int(num_questions)
        else:
            return redirect(url_for('home'))  # Redirect if no 'num_questions' is provided

        if num_questions > 10:  # Limit the number of questions to 10
            num_questions = 10

        # Create a list of placeholder questions based on the number provided by the user
        questions = [f"Question {i+1}" for i in range(num_questions)]
        return render_template('create-quiz.html', questions=questions, title=title)

    # Function to handle form submission
    def submit_quiz(self):
        if request.method == 'POST':
            title = request.form.get('title')
            # Count the number of questions submitted based on the 'question_text_' prefix
            num_questions = len([key for key in request.form if key.startswith('question_text_')])
            print(f"Title: {title}")

            # Process or store the data
            for i in range(num_questions):
                question_text = request.form[f'question_text_{i}']
                answer1 = request.form[f'answer_{i}_1']
                answer2 = request.form[f'answer_{i}_2']
                answer3 = request.form[f'answer_{i}_3']
                answer4 = request.form[f'answer_{i}_4']
                correct_answer = request.form[f'correct_answer_{i}']

                # For now, just print the data
                print(f"Question {i+1}: {question_text}")
                print(f"Options: {answer1}, {answer2}, {answer3}, {answer4}")
                print(f"Correct Answer: {correct_answer}")



            return redirect(url_for('home'))
