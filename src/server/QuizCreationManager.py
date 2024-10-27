from flask import request, render_template, redirect, url_for, session, flash

class QuizCreationManager:
    def __init__(self, db_manager):
        self.db_manager = db_manager

    def create_quiz(self):
        user_email = session['email']

        if self.has_reached_quiz_limit(user_email):
            flash("You have reached the maximum number of quizzes allowed (3).", "error")
            return redirect(url_for('create_quiz_route'))

        num_questions = request.form.get('num_questions')
        title = request.form.get('title')
        if num_questions:
            num_questions = int(num_questions)
        else:
            return redirect(url_for('home'))

        if num_questions > 10:
            num_questions = 10

        questions = [f"Question {i+1}" for i in range(num_questions)]
        return render_template('create-quiz.html', questions=questions, title=title, num_questions=num_questions)

    def submit_quiz(self):
        if request.method == 'POST':
            title = request.form.get('title')
            user_email = session['email']

            questions = []
            num_questions = 10
            for i in range(num_questions):
                question_text = request.form.get(f'question_text_{i}', None)
                if question_text:
                    option1 = request.form.get(f'answer_{i}_1')
                    option2 = request.form.get(f'answer_{i}_2')
                    option3 = request.form.get(f'answer_{i}_3')
                    option4 = request.form.get(f'answer_{i}_4')
                    correct_answer = request.form.get(f'correct_answer_{i}')
                    questions.append((question_text, option1, option2, option3, option4, correct_answer))

            columns = ['user_email', 'title']
            values = [user_email, title]
            query_values_placeholders = '%s, %s'

            for i in range(len(questions)):
                question_idx = i + 1
                columns += [
                    f'question{question_idx}', f'option{question_idx}_1', f'option{question_idx}_2', 
                    f'option{question_idx}_3', f'option{question_idx}_4', f'correct_option{question_idx}'
                ]
                query_values_placeholders += ', %s, %s, %s, %s, %s, %s'

                values.extend(questions[i])

            insert_quiz_query = f"INSERT INTO quizzes ({', '.join(columns)}) VALUES ({query_values_placeholders})"
            self.db_manager.execute_commit(insert_quiz_query, tuple(values))

            return redirect(url_for('home'))

    def has_reached_quiz_limit(self, user_email):
        query = "SELECT COUNT(*) FROM quizzes WHERE user_email = %s"
        result = self.db_manager.execute_query(query, (user_email,))
        return result[0][0] >= 3
