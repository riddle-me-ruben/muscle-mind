from flask import request, redirect, url_for, render_template, session, flash

class QuizManager:
    def __init__(self, db_manager, session):
        self.db_manager = db_manager
        self.session = session


    # Function to check if a user has reached the quiz creation limit
    def has_reached_quiz_limit(self, user_email):
        query = "SELECT COUNT(*) FROM quizzes WHERE user_email = %s"
        result = self.db_manager.execute_query(query, (user_email,))
        quiz_count = result[0][0]
        return quiz_count >= 3


    # Function to render the quiz creation form based on user input for the number of questions
    def create_quiz(self):
        user_email = self.session['email']  # Assuming you have user_id stored in the session

        # Check if the user has reached the quiz creation limit
        if self.has_reached_quiz_limit(user_email):
            flash("You have reached the maximum number of quizzes allowed (3).", "error")
            return redirect(url_for('create_quiz_route'))


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
            user_email = self.session['email']  # Assuming you have user_id stored in the session

            # Step 1: Insert the quiz into the 'quizzes' table
            insert_quiz_query = "INSERT INTO quizzes (user_email, title) VALUES (%s, %s)"
            self.db_manager.execute_commit(insert_quiz_query, (user_email, title))

            # Retrieve the last inserted quiz_id
            quiz_id = self.db_manager.get_last_insert_id()

            # Count the number of questions submitted based on the 'question_text_' prefix
            num_questions = len([key for key in request.form if key.startswith('question_text_')])

            # Step 2: Insert each question into the 'questions' table
            for i in range(num_questions):
                question_text = request.form[f'question_text_{i}']
                answer1 = request.form[f'answer_{i}_1']
                answer2 = request.form[f'answer_{i}_2']
                answer3 = request.form[f'answer_{i}_3']
                answer4 = request.form[f'answer_{i}_4']
                correct_answer = request.form[f'correct_answer_{i}']

                # Insert each question and its options into the 'questions' table
                insert_question_query = """
                INSERT INTO questions (quiz_id, question_text, option1, option2, option3, option4, correct_option)
                VALUES (%s, %s, %s, %s, %s, %s, %s)
                """
                self.db_manager.execute_commit(insert_question_query, (
                    quiz_id, question_text, answer1, answer2, answer3, answer4, correct_answer
                ))

            return redirect(url_for('home'))
